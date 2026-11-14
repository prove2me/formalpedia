-- Prove2me | solution 1 for AvramDividend.Classical.avram_b111_original_all_actual_positive_time_jump_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:30:09.835654+00:00
-- url     : https://prove2.me/submissions/72316fe9-1498-492a-a036-5ca005bbc017

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical original positive-time source jumps are nonpositive, from the actual no-positive-jumps structure field. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    X.X t ω -
      Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≤ 0 := by
  have hLim :=
    (avram_p2_a_zero_rate_original_cadlag_regular_all_times X ω).1 t
  have hNonpos := X.noPosJumps ω t
    (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t) ht hLim
  linarith
