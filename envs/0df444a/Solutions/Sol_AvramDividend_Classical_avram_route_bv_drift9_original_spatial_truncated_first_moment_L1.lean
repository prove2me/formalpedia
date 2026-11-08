-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:22:31.770883+00:00
-- url     : https://prove2.me/submissions/0fb905bb-cbc3-4b32-a335-74606df2b647

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntegrableOn (fun z : ℝ => min ε (-z)) (Iio (0 : ℝ)) X.ν := by
  have hint := chat07_bv_negative_jump_min_abs_integrable X hBV
  have hmem :
      ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ∈ Iio (0 : ℝ) :=
    ae_restrict_mem measurableSet_Iio
  change Integrable (fun z : ℝ => min ε (-z))
    (X.ν.restrict (Iio (0 : ℝ)))
  change Integrable (fun z : ℝ => min (1 : ℝ) |z|)
    (X.ν.restrict (Iio (0 : ℝ))) at hint
  apply hint.mono (measurable_const.min measurable_neg).aestronglyMeasurable
  filter_upwards [hmem] with z hz
  change z < (0 : ℝ) at hz
  have hznonneg : 0 ≤ -z := by linarith
  have hfnonneg : 0 ≤ min ε (-z) := le_min hε.le hznonneg
  have hfnonneg1 : 0 ≤ min (1 : ℝ) |z| :=
    le_min (by norm_num) (abs_nonneg z)
  have hcap : min ε (-z) ≤ min (1 : ℝ) |z| := by
    simpa [abs_of_neg hz] using (min_le_min hε1 (le_refl (-z)))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hfnonneg,
    abs_of_nonneg hfnonneg1] using hcap
