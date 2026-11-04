-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_zero_horizon_exact_nu_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:07:52.064371+00:00
-- url     : https://prove2.me/submissions/1a1bdc42-5227-431e-b917-39a7d0904225

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_zero_horizon_vanishes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact original-process zero-horizon rate, even if the mark set has infinite Levy mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 0 ×ˢ B) ∂P) =
      (0 : ℝ≥0∞) * X.ν B := by
  simpa using (avram_p2_a_zero_rate_original_zero_horizon_vanishes X B)
