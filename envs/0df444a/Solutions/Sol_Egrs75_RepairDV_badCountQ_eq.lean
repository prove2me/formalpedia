-- Prove2me | solution 1 for Egrs75.RepairDV.badCountQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:33.283575+00:00
-- url     : https://prove2.me/submissions/ae17c1b6-4206-4c3f-aa74-027b3abda674

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution (q n : ℕ) :
    badCountQ q n = ((Nat.digits q n).filter (fun d => bigQ q d)).length := rfl
end Egrs75.RepairDV
