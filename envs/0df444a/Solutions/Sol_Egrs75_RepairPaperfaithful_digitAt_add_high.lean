-- Prove2me | solution 1 for Egrs75.RepairPaperfaithful.digitAt_add_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:56.522939+00:00
-- url     : https://prove2.me/submissions/aba5a007-460d-4dc0-9c4b-35917058e6c8

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
theorem _root_.solution {p : ℕ} {k u h i : ℕ} (hu : u < p ^ k) (hki : k ≤ i) :
    digitAt p i (u + p ^ k * h) = digitAt p (i - k) h := by
  unfold digitAt
  have hpk0 : 0 < p ^ k := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hu; omega)
  -- (u + p^k*h)/p^i = h/p^(i-k):  divide by p^k first (quotient h since u<p^k), then p^(i-k)
  have hpk : p ^ i = p ^ k * p ^ (i - k) := by rw [← pow_add]; congr 1; omega
  have hdiv : (u + p ^ k * h) / p ^ k = h := by
    rw [Nat.add_mul_div_left _ _ hpk0, Nat.div_eq_of_lt hu, zero_add]
  rw [hpk, ← Nat.div_div_eq_div_mul, hdiv]
end Egrs75.RepairPaperfaithful
