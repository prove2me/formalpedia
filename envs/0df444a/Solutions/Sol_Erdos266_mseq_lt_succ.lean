-- Prove2me | solution 1 for Erdos266.mseq_lt_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:47:21.7375+00:00
-- url     : https://prove2.me/submissions/5cb55dde-b103-4aa6-8a76-5e1e9acb1cb8

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (d : ℕ) : mseq d < mseq (d + 1) :=
  lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
end Erdos266
