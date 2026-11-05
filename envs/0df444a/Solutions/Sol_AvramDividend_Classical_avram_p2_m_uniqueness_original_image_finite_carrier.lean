-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_original_image_finite_carrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:37:13.562756+00:00
-- url     : https://prove2.me/submissions/b486dfd6-3e90-47ee-b5b0-b3805f15aed3

import Mathlib.MeasureTheory.Measure.FiniteMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- A finite-mass compactly carried original image measure admits the exact
finite-measure representation used by the weak-convergence compactification. -/
theorem solution (μ : Measure ℝ)
    (hmass : μ Set.univ < ⊤)
    (hunit : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ρ : FiniteMeasure ℝ,
      (ρ : Measure ℝ) = μ ∧ ρ (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  haveI hfinite : IsFiniteMeasure μ := (isFiniteMeasure_iff μ).2 hmass
  have hzero : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
    (mem_ae_iff).1 hunit
  refine ⟨⟨μ, hfinite⟩, rfl, ?_⟩
  simpa only [FiniteMeasure.mk_apply, hzero, ENNReal.toNNReal_zero]
