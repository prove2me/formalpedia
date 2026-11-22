-- Prove2me | solution 1 for Egrs75.RepairDV.badCountQ_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:36.993+00:00
-- url     : https://prove2.me/submissions/7f1d07b2-3cad-47e6-b125-2f44fdb4e58a

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Theorems.Thm_Egrs75_RepairDV_badCountQ_eq
public import Theorems.Thm_Egrs75_RepairDV_digits_split

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution {q k Lo Hi : ℕ} (hq : 1 < q) (hLo : Lo < q ^ k) (hHi : 0 < Hi) :
    badCountQ q (Lo + q ^ k * Hi) = badCountQ q Lo + badCountQ q Hi := by
  rw [badCountQ_eq, badCountQ_eq, badCountQ_eq, digits_split hq hLo hHi]
  simp_all
end Egrs75.RepairDV
