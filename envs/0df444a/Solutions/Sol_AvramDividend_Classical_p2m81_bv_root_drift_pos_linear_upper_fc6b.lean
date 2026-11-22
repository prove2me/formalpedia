-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_root_drift_pos_linear_upper_fc6b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:24:01.096269+00:00
-- url     : https://prove2.me/submissions/ae77012f-22e1-4147-b35a-650b5f3bfa3a

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
    (hBV : X.BoundedVariation) :
    0 < X.drift ∧ ∀ θ : ℝ, 0 ≤ θ → X.ψ θ ≤ X.drift * θ := by
  have hψupper : ∀ θ : ℝ, 0 ≤ θ → X.ψ θ ≤ X.drift * θ := by
    intro θ hθ
    have hub := psi_upper_bound_by_compensated_small_jumps X θ hθ
    simp only [hBV.1, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div, add_zero] at hub
    have hsmall : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1 - θ * y) (Ioo (-1 : ℝ) 0) X.ν := by
      have hmem : ∀ y : ℝ, y ∈ Ioo (-1 : ℝ) 0 → y ∈ Iio (0 : ℝ) := fun _ hy => hy.2
      have hbase := (levy_compensated_jump_integrable_nonneg X θ hθ).mono_set hmem
      refine hbase.congr_fun (fun y hy => ?_) measurableSet_Ioo
      have hmid : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
      simp only [Set.indicator_of_mem hmid, mul_one]
    have hThetaNeg : IntegrableOn (fun y : ℝ => θ * (-y)) (Ioo (-1 : ℝ) 0) X.ν :=
      Integrable.const_mul (bv_small_negative_first_moment_integrable X hBV) θ
    have hPoint : ∀ y ∈ Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) ≤ θ * (-y) := by
      intro y hy
      have hexp : Real.exp (θ * y) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy.2))
      have hneg : θ * (-y) = -(θ * y) := by rw [mul_neg]
      linarith [hexp, hneg]
    have hmono : (∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) ∂X.ν)
        ≤ ∫ y in Ioo (-1 : ℝ) 0, θ * (-y) ∂X.ν :=
      integral_mono_ae hsmall hThetaNeg
        (ae_restrict_of_forall_mem measurableSet_Ioo (fun y hy => hPoint y hy))
    have hψle : X.ψ θ ≤ X.c * θ + (∫ y in Ioo (-1 : ℝ) 0, θ * (-y) ∂X.ν) := by
      linarith [hub, hmono]
    rw [integral_const_mul θ (fun y : ℝ => -y), integral_neg] at hψle
    rw [show X.drift = X.c - ∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν from rfl]
    nlinarith [hψle]
  have hdrift : 0 < X.drift := by
    have h := hψupper φ (le_of_lt hφ)
    rw [hroot] at h
    by_contra hle
    push_neg at hle
    have hmul : X.drift * φ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hφ)
    linarith [hq, h, hmul]
  exact ⟨hdrift, hψupper⟩
