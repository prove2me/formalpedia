-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_root_psi_quadratic_upper_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T04:55:19.694877+00:00
-- url     : https://prove2.me/submissions/a83b66e8-c20e-4157-b600-743a2238f8da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_upper_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ - q ≤ (|X.drift| + |q|) * (1 + θ ^ 2) := by
  have hub := psi_upper_bound_by_compensated_small_jumps X θ hθ
  simp only [hBV.1, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div, add_zero] at hub
  let k : ℝ → ℝ := fun y => Real.exp (θ * y) - 1 - θ * y
  have hsmall : IntegrableOn k (Ioo (-1 : ℝ) 0) X.ν := ((levy_compensated_jump_integrable_nonneg X θ hθ).mono_set fun _ hy => hy.2).congr_fun (fun y hy => by have hmid : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩; simp only [k, Set.indicator_of_mem hmid, mul_one]) measurableSet_Ioo
  have hThetaNeg : IntegrableOn (fun y : ℝ => θ * (-y)) (Ioo (-1 : ℝ) 0) X.ν := Integrable.const_mul (bv_small_negative_first_moment_integrable X hBV) θ
  have hPoint : ∀ y ∈ Ioo (-1 : ℝ) 0, k y ≤ θ * (-y) := fun y hy => by simp only [k]; linarith [Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy.2)), mul_neg θ y]
  have hψle : X.ψ θ ≤ X.c * θ + (∫ y in Ioo (-1 : ℝ) 0, θ * (-y) ∂X.ν) := by linarith [hub, integral_mono_ae hsmall hThetaNeg (ae_restrict_of_forall_mem measurableSet_Ioo (fun y hy => hPoint y hy))]
  have hψdrift : X.ψ θ ≤ X.drift * θ := by rw [integral_const_mul θ (fun y : ℝ => -y), integral_neg] at hψle; rw [show X.drift = X.c - ∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν from rfl] at ⊢; nlinarith [hψle]
  have hψq : X.ψ θ - q ≤ |X.drift| * θ + |q| := by linarith [hψdrift, le_abs_self (X.drift * θ), neg_le_abs q, show |X.drift * θ| = |X.drift| * θ from by rw [abs_mul, abs_of_nonneg hθ]]
  have hθle : θ ≤ 1 + θ ^ 2 := by nlinarith [sq_nonneg (θ - 1), hθ]
  have h1le : (1 : ℝ) ≤ 1 + θ ^ 2 := by nlinarith [sq_nonneg θ]
  have hFinal : |X.drift| * θ + |q| ≤ (|X.drift| + |q|) * (1 + θ ^ 2) := by have h := add_le_add (mul_le_mul_of_nonneg_left hθle (abs_nonneg X.drift)) (mul_le_mul_of_nonneg_left h1le (abs_nonneg q)); rw [mul_one] at h; nlinarith [h]
  linarith [hψq, hFinal]
