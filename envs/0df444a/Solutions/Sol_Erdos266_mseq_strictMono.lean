-- Prove2me | solution 1 for Erdos266.mseq_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:48:56.582832+00:00
-- url     : https://prove2.me/submissions/fe52d135-dcdf-4413-9a39-4ffb28afd345

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_mseq_lt_succ

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution : StrictMono mseq :=
  strictMono_nat_of_lt_succ mseq_lt_succ
end Erdos266
