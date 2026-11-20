-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_levy_psi_continuousOn_nonnegative_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:34:40.283123+00:00
-- url     : https://prove2.me/submissions/ad9ad1e6-6db7-4a0d-a01f-18dc7fa20d1d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_compensated_uniform_envelope
import Theorems.Thm_AvramDividend_Classical_psi_continuousOn_Icc_of_compensated_envelope
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℝ) (hB : 0 ≤ B) :
    ContinuousOn X.ψ (Icc (0 : ℝ) B) := by
  let f : ℝ → ℝ := fun y => min 1 (y ^ 2)
  have hfpos (y : ℝ) : 0 ≤ f y := by
    dsimp [f]
    exact le_min (by norm_num) (sq_nonneg _)
  have hfmeas : Measurable f := by
    dsimp [f]
    fun_prop
  have hf : Integrable f X.ν := by
    refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
    have hNorm (y : ℝ) : ‖f y‖ₑ = ENNReal.ofReal (f y) := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hfpos y)]
    change (∫⁻ y, ‖f y‖ₑ ∂X.ν) < ⊤
    simp_rw [hNorm]
    exact X.ν_integrable
  have hfRest : Integrable f (X.ν.restrict (Iio (0 : ℝ))) :=
    hf.integrableOn
  have hg : Integrable
      (fun y => (1 + B ^ 2) * min 1 (y ^ 2))
      (X.ν.restrict (Iio (0 : ℝ))) := by
    exact hfRest.const_mul (1 + B ^ 2)
  exact psi_continuousOn_Icc_of_compensated_envelope
    X B hB (fun y => (1 + B ^ 2) * min 1 (y ^ 2))
    hg (psi_compensated_uniform_envelope X B hB)
