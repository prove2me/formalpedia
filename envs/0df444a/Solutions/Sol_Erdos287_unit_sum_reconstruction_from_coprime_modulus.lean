-- Prove2me | solution 1 for Erdos287.unit_sum_reconstruction_from_coprime_modulus
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:54:22.803063+00:00
-- url     : https://prove2.me/submissions/e706ab9c-085a-44cc-ac74-788685ec6e84

import Mathlib
import Theorems.Thm_Erdos287_reciprocal_clearing_and_modular_reduction

open Finset

set_option autoImplicit false

/-- A single sufficiently large modulus coprime to the common denominator
detects exact unit-fraction equality. -/
theorem solution (D : Finset ℕ) (L q : ℕ) (hL : 0 < L) (hcop : L.Coprime q)
    (hD : ∀ n ∈ D, n ∣ L)
    (hbound : Int.natAbs (((∑ n ∈ D, L / n : ℕ) : ℤ) - L) < q) :
    (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔ (∑ n ∈ D, (n : ZMod q)⁻¹) = 1 := by
  obtain ⟨hrat, hmod⟩ := Erdos287.reciprocal_clearing_and_modular_reduction D q L hL hcop hD
  rw [hrat, hmod]
  let W := ∑ n ∈ D, L / n
  change W = L ↔ W ≡ L [MOD q]
  constructor
  · intro h
    rw [h]
  · intro h
    let a := (W : ℤ) - L
    have hdiv : (q : ℤ) ∣ a := Nat.modEq_iff_dvd.mp h.symm
    have hz : a = 0 := by
      by_contra! hne
      have ha := Int.natAbs_pos.mpr hne
      have hnat : q ∣ a.natAbs := by
        simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv
      exact (not_le_of_gt hbound) (Nat.le_of_dvd ha hnat)
    dsimp [a] at hz
    omega

