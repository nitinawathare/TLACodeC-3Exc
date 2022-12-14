-------------------------- MODULE DolevStrong_exc --------------------------

(*This assignment is designed as a part of a take-home exercise for the C-3 workshop*)
(*Author : Nitin Awathare*)

EXTENDS FiniteSets, Naturals, Integers

CONSTANT RM  \* The set of nodes
CONSTANT F   \* set of faulty nodes.

VARIABLES
  nodeState,  
  nodeRound,  
  nodeConvincedValue,   
  leaderState,   
  msgs           
    
Messages ==
 
  [type : {"1", "0", " "}]  \cup  [nodeMsg: {"true"}, type : {"0", "1"}, rm : RM, sign: {RM}]
   
DSTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ nodeState \in {"init", "convinced"}
  /\ nodeRound \in [RM -> 0 .. F+1]
  /\ leaderState \in {"init", "sent"}
  /\ nodeConvincedValue \in {"0", "1", " "}
  /\ msgs \subseteq Messages

DSInit ==   
  (*************************************************************************)
  (* The initial predicate                                                 *)
  (*************************************************************************)
  /\ nodeState = [r \in RM |-> "init"]
  /\ nodeRound = [r \in RM |-> 1]
  /\ nodeConvincedValue = [r \in RM |-> -1]
  /\ leaderState = "init"
  /\ msgs = {}

-----------------------------------------------------------------------------


LeaderSend ==
  (*************************************************************************)
  (* Leader Broadcasts two types of messages. *)
  (*************************************************************************)
   TRUE (*Remove TRUE and add your code here*)


 
NodeRcv1FromLeader(r) == 
  (*************************************************************************)
  (* Node r receives a message of type 1 from the leader. *)
  (*************************************************************************)
   TRUE (*Remove TRUE and add your code here*)

  
 NodeRcv0FromLeader(r) == 
  (*************************************************************************)
  (* Node r receives a message of type 0 from the leader. *)
  (*************************************************************************)
   TRUE (*Remove TRUE and add your code here*)

  
NodeRcvNothingFromLeader(r) == 
  (*************************************************************************)
  (* The leader doesn't send any message to node r*)
  (*************************************************************************)
   TRUE (*Remove TRUE and add your code here*)

  


canConvincedNode(msg, r) ==  
  (*************************************************************************)
  (* Node r is convinced of the message msg.*)
  (*************************************************************************)
   TRUE (*Remove TRUE and add your code here*)

    
  
NodeRcvFromOtherNode(r) == 
  (*************************************************************************)
  (* Node r receives a message msg from some other node n*)
  (* From here, you should call canConvincedNode(msg, r) function*)
  (*************************************************************************)
  TRUE (*Remove TRUE and add your code here*)

  
DSNext ==
  \/ LeaderSend
  \/ \E r \in RM : 
       NodeRcv1FromLeader(r) \/ NodeRcv0FromLeader(r) \/ NodeRcvNothingFromLeader(r) 
  \/ \E r, n \in RM : NodeRcvFromOtherNode(r) 
   

 TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two honest nodes have not arrived at *)
  (* conflicting decisions.  It is an invariant of the specification.      *)
  (* Note that you have to check this only for honest nodes.               *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ nodeState[r1] = "convinced"
                       /\ nodeState[r2] = "convinced"
                       /\ nodeConvincedValue[r1] # nodeConvincedValue[r2]
  

=============================================================================
\* Modification History
\* Last modified Wed Dec 14 13:43:35 SGT 2022 by nitina
\* Created Tue Dec 13 14:24:35 SGT 2022 by nitina
