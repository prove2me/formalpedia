-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_summable_L2_step_differences_centered_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:01:58.760345+00:00
-- url     : https://prove2.me/submissions/4c8e4409-db6f-40a9-b145-9c1371eb38e8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Summable consecutive L² distances are an explicit original-source
Cauchy certificate and preserve centred expectations at the limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSteps : Summable (fun k => dist (M k) (M (k + 1))))
    (hCentered : ∀ k, (∫ ω, M k ω ∂P) = 0) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by
  have hCauchy : CauchySeq M := cauchySeq_of_summable_dist hSteps
  exact avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
    X M hCauchy hCentered
