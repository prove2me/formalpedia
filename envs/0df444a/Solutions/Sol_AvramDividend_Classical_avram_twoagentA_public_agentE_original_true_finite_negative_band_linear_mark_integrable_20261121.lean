-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_agentE_original_true_finite_negative_band_linear_mark_integrable_20261121
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:23:33.670881+00:00
-- url     : https://prove2.me/submissions/06a6ff3d-122c-4bda-96e1-81dff06bbf74

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Original finite negative-band physical Lévy mark has finite first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) :
    IntegrableOn (fun z : ℝ => z)
      (Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) X.ν := by
  let δ : ℝ := 1 / ((m : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hrate : X.ν (Iic (-δ)) < ⊤ :=
    negative_jump_truncation_measure_finite X.ν X.ν_integrable δ hδ
  have hsub : Ioc (-(1 / ((n : ℝ) + 1))) (-δ) ⊆ Iic (-δ) := by
    intro z hz
    exact hz.2
  have hfinite : X.ν (Ioc (-(1 / ((n : ℝ) + 1))) (-δ)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsub) hrate)
  have hmeas : AEStronglyMeasurable (fun z : ℝ => z) X.ν :=
    measurable_id.aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(X.ν.restrict
      (Ioc (-(1 / ((n : ℝ) + 1))) (-δ))), ‖(z : ℝ)‖ ≤ (1 : ℝ) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro z hz
    have hnpos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ hden).2 (by nlinarith)
    have hzNeg : z ≤ 0 :=
      le_trans hz.2 (neg_nonpos.mpr (le_of_lt hδ))
    have hzLower : -1 ≤ z := by linarith [hz.1, hfrac]
    rw [Real.norm_eq_abs, abs_of_nonpos hzNeg]
    linarith
  simpa only [δ] using
    (X.ν.integrableOn_of_bounded hfinite hmeas hbound)
