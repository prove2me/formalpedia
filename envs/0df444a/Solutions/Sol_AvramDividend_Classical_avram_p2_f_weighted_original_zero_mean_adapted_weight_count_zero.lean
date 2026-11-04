-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_zero_mean_adapted_weight_count_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:15:36.362817+00:00
-- url     : https://prove2.me/submissions/f6110bb8-a1b9-4ecf-b3fd-376a3215b596

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- An original past-adapted nonnegative weight with zero mean makes
its genuine future marked jump-count expected contribution zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (hZero : (∫⁻ ω, H ω ∂P) = 0) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) = 0 := by
  rw [avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor
    X s t hst B hB H hH, hZero]
  simp
