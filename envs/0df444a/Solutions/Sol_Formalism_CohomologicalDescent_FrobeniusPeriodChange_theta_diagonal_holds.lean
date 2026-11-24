-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.theta_diagonal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:24:00.374252+00:00
-- url     : https://prove2.me/submissions/a642c000-1d8f-4128-a481-e01afc8673e7

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_gamma_laws_hold
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_gammaSeries_zero_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : ThetaDiag := by
  intro k _ un g c w κ heq
  obtain ⟨hadd, hmul, hC, -, hX, -, hcc0⟩ := gamma_laws_hold k 0 un
  have e1 : ∀ f : k⟦X⟧, coeff 1 (X * f) = constantCoeff f := by
    intro f
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y := by
    intro y
    obtain ⟨q, hq⟩ : X ∣ y - C (constantCoeff y) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have e : y = C (constantCoeff y) + X * q := by rw [← hq]; ring
    rw [e, hadd, hmul, hC, hX]
    rw [map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]
    rw [mul_assoc, e1, e1, map_mul, hcc0]
    simp
  have hc1 : ∀ f q : k⟦X⟧, coeff 1 (f * q) = coeff 1 f * constantCoeff q + constantCoeff f * coeff 1 q := by
    intro f q
    first
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply])
    | (rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul, Finset.Nat.antidiagonal_succ];
        simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply])
  have hV : IsUnit (1 + un * X : k⟦X⟧) := by
    first
    | (rw [isUnit_iff_constantCoeff]; simp)
    | exact isUnit_iff_constantCoeff.2 (by simp)
  set V := hV.unit with hVdef
  have hV0 : constantCoeff (V : k⟦X⟧) = 1 := by rw [IsUnit.unit_spec]; simp
  have hV1' : coeff 1 (V : k⟦X⟧) = constantCoeff un := by
    rw [IsUnit.unit_spec, map_add, coeff_one, if_neg one_ne_zero, zero_add, mul_comm, e1]
  have hgs : gamSer 0 un = X * (V : k⟦X⟧) := by rw [gammaSeries_zero_eq, IsUnit.unit_spec]
  have hVcc : ∀ m : ℤ, constantCoeff ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    intro m
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow]
    · rw [zpow_neg, zpow_natCast, map_units_inv, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow,
        inv_one]
  have hVn : ∀ n : ℕ, coeff 1 ((V : k⟦X⟧) ^ n) = n * constantCoeff un := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hc1, ih, hV1', map_pow, hV0, one_pow]
      push_cast
      ring
  have hV1 : ∀ m : ℤ, coeff 1 ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = m * constantCoeff un := by
    intro m
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, Units.val_pow_eq_pow_val, hVn, Int.cast_natCast]
    · have hcc_inv : constantCoeff (((V ^ n)⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
        rw [map_units_inv, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow, inv_one]
      have hinv := hc1 ((V ^ n : (k⟦X⟧)ˣ) : k⟦X⟧) (((V ^ n)⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
      rw [Units.mul_inv, coeff_one, if_neg one_ne_zero, hcc_inv, Units.val_pow_eq_pow_val, hVn,
        map_pow, hV0, one_pow] at hinv
      rw [zpow_neg, zpow_natCast]
      push_cast
      linear_combination -hinv
  let φ : k⟦X⟧ →+* LaurentSeries k := HahnSeries.ofPowerSeries ℤ k
  have hφ : Function.Injective φ := HahnSeries.ofPowerSeries_injective
  have hx : φ X ≠ 0 := (map_ne_zero_iff φ hφ).2 X_ne_zero
  have hVz : ∀ m : ℤ, φ ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = φ (V : k⟦X⟧) ^ m := by
    intro m
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, map_units_inv, Units.val_pow_eq_pow_val,
        map_pow]
  have hc : c = gam0 0 un (w : k⟦X⟧) * ((V ^ κ : (k⟦X⟧)ˣ) : k⟦X⟧) * (1 + X * g) *
      ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) := by
    apply hφ
    have hw : φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hxk : φ X ^ κ ≠ 0 := zpow_ne_zero κ hx
    change φ (gam0 0 un (w : k⟦X⟧)) * φ (gamSer 0 un) ^ κ * φ (1 + X * g) =
      φ c * φ (w : k⟦X⟧) * φ X ^ κ at heq
    rw [hgs, map_mul, mul_zpow] at heq
    apply mul_right_cancel₀ hxk
    simp only [map_mul, hVz]
    calc φ c * φ X ^ κ = φ c * φ X ^ κ * (φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)) := by
          rw [hw, mul_one]
      _ = (φ c * φ (w : k⟦X⟧) * φ X ^ κ) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) := by ring
      _ = _ := by rw [← heq]; ring
  have hww0 : constantCoeff (w : k⟦X⟧) * constantCoeff ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hww1 : coeff 1 (w : k⟦X⟧) * constantCoeff ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) +
      constantCoeff (w : k⟦X⟧) * coeff 1 ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 0 := by
    rw [← hc1, Units.mul_inv, coeff_one, if_neg one_ne_zero]
  have hC1 : coeff 1 (1 + X * g) = constantCoeff g := by
    rw [map_add, coeff_one, if_neg one_ne_zero, zero_add, e1]
  have hC0 : constantCoeff (1 + X * g) = 1 := by simp
  rw [hc]
  refine ⟨?_, ?_⟩
  · simp only [map_mul, hcc0, hVcc, hC0, mul_one]
    exact hww0
  · simp only [hc1, map_mul, h1, hcc0, hVcc, hV1, hC0, hC1]
    linear_combination hww1 + ((κ : k) * constantCoeff un + constantCoeff g) * hww0
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
