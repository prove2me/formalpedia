-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_centered_uncentered_jump_delta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:54:10.012504+00:00
-- url     : https://prove2.me/submissions/e07f5b0b-0d87-48ba-8062-e203947dbfc4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

/-- The genuine original source jump at positive time is unchanged by
subtracting its initial reserve before taking the left limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (hu : 0 < u) :
    (X.X u ω - X.X 0 ω) -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω - X.X 0 ω) u =
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by
  simpa only [X.X_zero ω, sub_zero]
