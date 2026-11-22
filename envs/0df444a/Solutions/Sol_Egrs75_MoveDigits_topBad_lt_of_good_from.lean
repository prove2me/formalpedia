-- Prove2me | solution 1 for Egrs75.MoveDigits.topBad_lt_of_good_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:39:45.520575+00:00
-- url     : https://prove2.me/submissions/bdb9032b-9ffd-470e-8188-d617b3489969

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Theorems.Thm_P2M_Egrs75_MoveDigits_mem_badIndexSet_iff__e33fc9bbbd0e
public import Theorems.Thm_Egrs75_RepairDV_topBadIndex_mem


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MoveDigits
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.MoveDigits
theorem _root_.solution {q n x : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hgood : ∀ idx, x ≤ idx → n / q ^ idx % q ≤ (q - 1) / 2) :
    topBadIndex q n < x := by
  by_contra hcon
  push Not at hcon
  have hmem := topBadIndex_mem hq hbad
  rw [mem_badIndexSet_iff' hq] at hmem
  unfold BadAt digitAt at hmem
  have := hgood _ hcon
  omega
end Egrs75.MoveDigits
