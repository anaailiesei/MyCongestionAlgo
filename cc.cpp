// -*- c-basic-offset: 4; indent-tabs-mode: nil -*- 
#include <math.h>
#include <iostream>
#include <algorithm>
#include <limits> 
#include <cmath>
#include <unordered_map>
#include <queue>
#include "cc.h"
#include "queue.h"
#include <stdio.h>
#include "switch.h"
#include "ecn.h"
using namespace std;

////////////////////////////////////////////////////////////////
//  CC SOURCE. Aici este codul care ruleaza pe transmitatori. Tot ce avem nevoie pentru a implementa
//  un algoritm de congestion control se gaseste aici.
////////////////////////////////////////////////////////////////
int CCSrc::_global_node_count = 0;
unordered_map<int, queue<Packet*>> packets;
int contor = 0;

CCSrc::CCSrc(EventList &eventlist)
    : EventSource(eventlist,"cc"), _flow(NULL)
{
    _mss = Packet::data_packet_size();
    _acks_received = 0;
    _nacks_received = 0;

    _highest_sent = 0;
    _next_decision = 0;
    _flow_started = false;
    _sink = 0;
  
    _node_num = _global_node_count++;
    _nodename = "CCsrc " + to_string(_node_num);

    _cwnd = 10 * _mss;
    _ssthresh = 0xFFFFFFFFFF;
    _flightsize = 0;
    _flow._name = _nodename;

    _fast_convergence = true;
    _beta = 0.1425;
    _c = 0.4;
    _c_prim = 2.0 / (1 + 1.0 / 8 * _beta) * _c;
    _d = 2 - _beta / 4 / (1 + 1.0 / 8 * _beta);
    _tcp_friendliness = true;
    _minD = 0;
    _epoch_start = 0;
    _w_last_max = 0;
    _origin_point = 0;
    _w_tcp = 0;
    _k = 0;
    _cnt = 0;
    _cwnd_cnt = 0;
    _ack_cnt = 0;

    lastRoundMinRTT = std::numeric_limits<simtime_picosec>::max();
    currentRoundMinRTT = std::numeric_limits<simtime_picosec>::max();
    cssBaselineMinRtt = std::numeric_limits<simtime_picosec>::max();
    rttSampleCount = 0;
    inCSS = false;
    cssRounds = 0;

    MIN_RTT_THRESH = 1e9; // 4 msec in picoseconds
    MAX_RTT_THRESH = 5e9; // 16 msec in picoseconds
    N_RTT_SAMPLE = 5;
    CSS_GROWTH_DIVISOR = 4;
    CSS_ROUNDS = 3;

    _quant_size = 2 * _mss;
    _quant_deficit = _quant_size;
    cubicReset();
    setName(_nodename);
}

void CCSrc::cubicReset() {
    _minD = 0;
    _epoch_start = 0;
    _w_last_max = 0;
    _origin_point = 0;
    _w_tcp = 0;
    _k = 0;
    _acks_received = 0;
}

/* Porneste transmisia fluxului de octeti */
void CCSrc::startflow(){
    cout << "Start flow " << _flow._name << " at " << timeAsSec(eventlist().now()) << "s" << endl;
    _flow_started = true;
    _highest_sent = 0;
    _packets_sent = 0;

    while (_flightsize + _mss < _cwnd)
        send_packet();
}

/* Initializeaza conexiunea la host-ul sink */
void CCSrc::connect(Route* routeout, Route* routeback, CCSink& sink, simtime_picosec starttime) {
    assert(routeout);
    _route = routeout;
    
    _sink = &sink;
    _flow._name = _name;
    _sink->connect(*this, routeback);

    eventlist().sourceIsPending(*this,starttime);
}

/* Variabilele cu care vom lucra:
    _nacks_received => 
    __acks_received
    _flightsize -> numarul de bytes aflati in zbor
    _mss -> maximum segment size
    _next_decision 
    _highest_sent
    _cwnd
    _ssthresh
    
    CCAck._ts -> timestamp ACK
    eventlist.now -> timpul actual
    eventlist.now - CCAck._tx -> latency
    
    ack.ackno();
    
    > Puteti include orice alte variabile in restul codului in functie de nevoie.
*/
/* TODO: In mare parte aici vom avea implementarea algoritmului si in functie de nevoie in celelalte functii */


// FLAG: Am adugat asta pt a calcula RTT ul unui ACK sau NACK
uint32_t CCSrc::latencyResponse(simtime_picosec ts) {
    return eventlist().now() - ts;
}

void CCSrc::packetLoss() {
    _epoch_start = 0;
    if (_cwnd < _w_last_max && _fast_convergence) {
        _w_last_max = _cwnd * (2 - _beta) / 2;
    } else {
        _w_last_max = _cwnd;
    }
    _cwnd *= (1 - _beta);
    _ssthresh = _cwnd;
    _next_decision = _highest_sent + _cwnd;
}

void CCSrc::onAck(simtime_picosec ts) {
    double rtt = latencyResponse(ts);
    if (_minD)
        _minD = std::min(_minD, rtt);
    else
        _minD = rtt;

    if (_cwnd <= _ssthresh) {
        _cwnd += _mss;

        if (!inCSS) {
            hystartUpdate(rtt);
        }
    } else {
        if (inCSS) {
            hystartCSS(rtt);
        } else {
            cubicUpdate(ts, rtt / 1e9);
            if (_cwnd_cnt > _cnt) {
                _cwnd += _mss;
                _cwnd_cnt = 0;
            } else {
                _cwnd_cnt += _mss;
            }
        }
    }
}


void CCSrc::hystartCSS(simtime_picosec rtt) {
    currentRoundMinRTT = std::min(currentRoundMinRTT, rtt);
    rttSampleCount++;

    _cwnd += (_mss / CSS_GROWTH_DIVISOR);

    if (rttSampleCount >= N_RTT_SAMPLE) {
        if (currentRoundMinRTT < cssBaselineMinRtt) {
            cssBaselineMinRtt = std::numeric_limits<simtime_picosec>::max();
            inCSS = false;
        } else {
            cssRounds++;
            if (cssRounds >= CSS_ROUNDS) {
                inCSS = false;
                _ssthresh = _cwnd; // Transition to congestion avoidance
            }
        }
        hystartReset();
    }
}


void CCSrc::cubicUpdate(simtime_picosec ts, double rtt) {
    ++_ack_cnt;

    double t = ts + _minD - _epoch_start;
    if (_epoch_start <= 0) {
        _epoch_start = ts;
        if (_cwnd < _w_last_max) {
            _k = pow(_w_last_max * _beta / _c, 1.0 / 3);
            _origin_point = _w_last_max;
        } else {
            _k = 0;
            _origin_point = _cwnd;
        }
        _ack_cnt = 1;
        _w_tcp = _cwnd;
    }
    
    // FLAG: Shpuld this be *mss?
    // double target = (_origin_point + _c_prim * pow(t / 2e9 - _k, 3)) / _d;
    double target = _origin_point + _c * pow(t / 1e9 - _k, 3);
    if (target > _cwnd) {
        _cnt = _cwnd / (target - _cwnd);
    } else {
        _cnt = 100 * _cwnd;
    }

    if (_tcp_friendliness) {
        cubicTcpFriendliness();
    }
}

void CCSrc::cubicTcpFriendliness() {
    _w_tcp += (3 * _beta / (2 - _beta) * _ack_cnt  * _mss) / _cwnd;

     _ack_cnt = 0;
     if (_w_tcp > _cwnd) {
         double max_cnt = _cwnd / (_w_tcp - _cwnd);
        if (_cnt > max_cnt) {
            _cnt = max_cnt;
        }
     }
}


//Aceasta functie este apelata atunci cand dimensiunea cozii a fost depasita iar packetul cu numarul de secventa ackno a fost aruncat.
void CCSrc::processNack(const CCNack& nack){ 
    //cout << "CC " << _name << " got NACK " <<  nack.ackno() << _highest_sent << " at " << timeAsMs(eventlist().now()) << " us" << endl;    
    _nacks_received ++;    
    _flightsize -= _mss;    
    
    if (nack.ackno()>=_next_decision) {
        CCSrc::packetLoss();
    }    
}  

void CCSrc::hystartReset() {
    lastRoundMinRTT = currentRoundMinRTT;
    currentRoundMinRTT = std::numeric_limits<simtime_picosec>::max();
    rttSampleCount = 0;
}

void CCSrc::hystartUpdate(simtime_picosec rtt) {
    currentRoundMinRTT = std::min(currentRoundMinRTT, rtt);
    rttSampleCount++;

    if (rttSampleCount >= N_RTT_SAMPLE && 
        currentRoundMinRTT != std::numeric_limits<simtime_picosec>::max() &&
        lastRoundMinRTT != std::numeric_limits<simtime_picosec>::max()) {
        
        simtime_picosec rttThresh = lastRoundMinRTT / 8;

        // Ensure rttThresh is within the MIN_RTT_THRESH and MAX_RTT_THRESH bounds
        if (rttThresh < MIN_RTT_THRESH) {
            rttThresh = MIN_RTT_THRESH;
        } else if (rttThresh > MAX_RTT_THRESH) {
            rttThresh = MAX_RTT_THRESH;
        }
        
        if (currentRoundMinRTT >= (lastRoundMinRTT + rttThresh)) {
            cssBaselineMinRtt = currentRoundMinRTT;
            inCSS = true;
            cssRounds = 0;

            // Exit slow start and enter CSS
            _ssthresh = _cwnd;
        }
    }
}

    
/* Process an ACK.  Mostly just housekeeping*/    
void CCSrc::processAck(const CCAck& ack) {
    CCAck::seq_t ackno = ack.ackno();    
    
    _acks_received++;    
    _flightsize -= _mss;    

    if (ack.is_ecn_marked()){
        //Atunci cand un packet pleaca pe fir, el va fi marcat ECN doar daca dimensiunea cozii este mai mare decat threshold-ul ECN setat. Receptorul va copia acest marcaj in pachetul ACK. Transmitatorul poate lua in calcul reducerea ratei, ca in exemplul mai jos. 
        if (ackno >=_next_decision){            
            packetLoss();
        }
    }
    else {
        //pachetul nu a fost marcat, putem creste rata.
        onAck(ack.ts());
    }
    
    //cout << "CWNDI " << _cwnd/_mss << endl;    
}    


/* Functia de receptie, in functie de ce primeste cheama processLoss sau processACK */
void CCSrc::receivePacket(Packet& pkt) 
{
    if (!_flow_started){
        return; 
    }

    switch (pkt.type()) {
    case CCNACK: 
        processNack((const CCNack&)pkt);
        pkt.free();
        break;
    case CCACK:
        processAck((const CCAck&)pkt);
        pkt.free();
        break;
    default:
        cout << "Got packet with type " << pkt.type() << endl;
        abort();
    }


    //now send packets!
    while (_flightsize + _mss < _cwnd)
        send_packet();
}

// Note: the data sequence number is the number of Byte1 of the packet, not the last byte.
/* Functia care se este chemata pentru transmisia unui pachet */
void CCSrc::send_packet() {
    CCPacket* p = NULL;

    assert(_flow_started);

    p = CCPacket::newpkt(*_route,_flow, _highest_sent+1, _mss, eventlist().now());
    _highest_sent += _mss;
    _packets_sent++;

    _flightsize += _mss;
    _quant_deficit -= _mss;

    //cout << "Sent " << _highest_sent+1 << " Flow Size: " << _flow_size << " Flow " << _name << " time " << timeAsUs(eventlist().now()) << endl;
    p->sendOn();
}

void CCSrc::doNextEvent() {
    if (!_flow_started){
      startflow();
      return;
    }
}

////////////////////////////////////////////////////////////////
//  CC SINK Aici este codul ce ruleaza pe receptor, in mare nu o sa aducem multe modificari
////////////////////////////////////////////////////////////////

/* Only use this constructor when there is only one for to this receiver */
CCSink::CCSink()
    : Logged("CCSINK"), _total_received(0) 
{
    
    _nodename = "CCsink";
    _total_received = 0;
}

/* Connect a src to this sink. */ 
void CCSink::connect(CCSrc& src, Route* route)
{
    _src = &src;
    _route = route;
    setName(_src->_nodename);
}


// Receive a packet.
// seqno is the first byte of the new packet.
void CCSink::receivePacket(Packet& pkt) {
    switch (pkt.type()) {
    case CC:
        break;
    default:
        abort();
    }

    CCPacket *p = (CCPacket*)(&pkt);
    CCPacket::seq_t seqno = p->seqno();

    simtime_picosec ts = p->ts();
    //bool last_packet = ((CCPacket*)&pkt)->last_packet();

    if (pkt.header_only()){
        send_nack(ts,seqno);      
    
        p->free();

        //cout << "Wrong seqno received at CC SINK " << seqno << " expecting " << _cumulative_ack << endl;
        return;
    }

    int size = p->size()-ACKSIZE; 
    _total_received += Packet::data_packet_size();

    bool ecn = (bool)(pkt.flags() & ECN_CE);

    send_ack(ts,seqno,ecn);
    // have we seen everything yet?
    pkt.free();
}

void CCSink::send_ack(simtime_picosec ts,CCPacket::seq_t ackno,bool ecn) {
    CCAck *ack = 0;
    ack = CCAck::newpkt(_src->_flow, *_route, ackno,ts,ecn);
    ack->sendOn();
}

void CCSink::send_nack(simtime_picosec ts, CCPacket::seq_t ackno) {
    CCNack *nack = NULL;
    nack = CCNack::newpkt(_src->_flow, *_route, ackno,ts);
    nack->sendOn();
}