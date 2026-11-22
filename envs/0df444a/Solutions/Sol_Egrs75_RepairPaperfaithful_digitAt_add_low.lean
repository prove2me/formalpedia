-- Prove2me | solution 1 for Egrs75.RepairPaperfaithful.digitAt_add_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:23.503172+00:00
-- url     : https://prove2.me/submissions/4c7deee0-4cf6-46e5-bfcd-df9df7fd9433

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairPaperfaithful
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairPaperfaithful
theorem _root_.solution {p : ℕ} (hp : 1 ≤ p) {k u h i : ℕ} (hik : i < k) :
    digitAt p i (u + p ^ k * h) = digitAt p i u := by
  unfold digitAt
  -- p^k * h = (p * (p^(k-i-1) * h)) * p^i, so the high block is (p*c) * p^i
  set c := p ^ (k - (i + 1)) * h with hc
  have hsplit : p ^ k * h = (p * c) * p ^ i := by
    have : p * c * p ^ i = p ^ (1 + (k - (i + 1)) + i) * h := by
      rw [hc]; rw [pow_add, pow_add, pow_one]; ring
    rw [this]; congr 2; omega
  rw [hsplit, Nat.add_mul_div_right _ _ (pow_pos (by omega) i),
      Nat.add_mul_mod_self_left]
end Egrs75.RepairPaperfaithful
