-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys71_original_no_intrinsic_mark_path_equals_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:22:57.519216+00:00
-- url     : https://prove2.me/submissions/0f98319a-c3f8-4902-8062-641f9daade88

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the original BV path, vanishing removed-jump sum leaves only drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, t ≤ T →
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = 0) →
      ∀ t : ℝ≥0, t ≤ T → X.X t ω = (t : ℝ) * X.drift := by
  have hR := avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV
  filter_upwards [hR] with ω hω
  intro hJ t ht
  have h := hω t
  rw [hJ t ht] at h
  simp only [sub_zero] at h
  linarith
