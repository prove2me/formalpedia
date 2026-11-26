-- Prove2me | solution 1 for Erdos287.unit_sum_reconstruction_from_absent_primes
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:52:58.293905+00:00
-- url     : https://prove2.me/submissions/92ae8a01-8143-490e-aa8d-81922695f089

import Mathlib
import Theorems.Thm_Erdos287_reciprocal_clearing_and_modular_reduction

open Finset

set_option autoImplicit false

/-- Exact equality is recovered from inverse sums at absent primes once
their product exceeds the magnitude of the cleared numerator error. -/
theorem solution (D P : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hD : ∀ n ∈ D, n ∣ L) (hP : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ L)
    (hbound : Int.natAbs (((∑ n ∈ D, L / n : ℕ) : ℤ) - L) < ∏ p ∈ P, p) :
    (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔
      ∀ p ∈ P, (∑ n ∈ D, (n : ZMod p)⁻¹) = 1 := by
  let W := ∑ n ∈ D, L / n
  let a := (W : ℤ) - L
  have hrat : (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔ W = L :=
    (Erdos287.reciprocal_clearing_and_modular_reduction D 1 L hL (by simp) hD).1
  have hmod (p : ℕ) (hp : p ∈ P) :
      (∑ n ∈ D, (n : ZMod p)⁻¹) = 1 ↔ W ≡ L [MOD p] := by
    have hcop := ((hP p hp).1.coprime_iff_not_dvd.mpr (hP p hp).2).symm
    exact (Erdos287.reciprocal_clearing_and_modular_reduction D p L hL hcop hD).2
  constructor
  · intro h p hp
    apply (hmod p hp).mpr
    rw [hrat.mp h]
  · intro h
    have hprod : ((∏ p ∈ P, p : ℕ) : ℤ) ∣ a := by
      rw [Nat.cast_prod]
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro p hp q hq hpq
        exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hP p hp).1 (hP q hq).1).mpr hpq)
      · intro p hp
        exact Nat.modEq_iff_dvd.mp ((hmod p hp).mp (h p hp)).symm
    have hzero : a = 0 := by
      by_contra hne
      have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr hne
      have hd := Int.natAbs_dvd_natAbs.mpr hprod
      have hle := Nat.le_of_dvd hpos hd
      have hlt : a.natAbs < ∏ p ∈ P, p := hbound
      simp only [Int.natAbs_natCast] at hle
      exact hlt.not_ge hle
    apply hrat.mpr
    dsimp [a] at hzero
    omega

