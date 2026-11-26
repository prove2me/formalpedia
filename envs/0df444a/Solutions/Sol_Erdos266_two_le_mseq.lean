-- Prove2me | solution 1 for Erdos266.two_le_mseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:48:50.40623+00:00
-- url     : https://prove2.me/submissions/3ab8967b-e6de-44b7-a89a-3c4f85d0c204

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
theorem _root_.solution (d : ℕ) : 2 ≤ mseq d := by
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact le_trans ih (mseq_lt_succ d).le
end Erdos266
