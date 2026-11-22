-- Prove2me | solution 1 for Egrs75.RepairDV.highBlock_lowDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:40:20.01373+00:00
-- url     : https://prove2.me/submissions/f7500a5f-2372-40d3-82a9-3011aa0c9de1

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Theorems.Thm_Egrs75_RepairDV_digit_good_above_top

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    LowDigits q (n / q ^ (topBadIndex q n + 1)) := by
  set k := topBadIndex q n + 1 with hk
  unfold LowDigits
  intro d hd
  -- `d` is the `i`-th digit of `Hi` for some `i < length`, hence the `(k+i)`-th of `n`.
  obtain ⟨i, hilt, hget⟩ := List.mem_iff_getElem.mp hd
  have hdval : d = (n / q ^ k) / q ^ i % q := by
    rw [← getD_digits (n / q ^ k) i (by omega), List.getD_eq_getElem _ 0 hilt, hget]
  -- `(n / q^k) / q^i = n / q^(k+i)`
  have hdiv : (n / q ^ k) / q ^ i = n / q ^ (k + i) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
  rw [hdval, hdiv]
  exact digit_good_above_top hq hbad (by omega)
end Egrs75.RepairDV
