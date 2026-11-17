-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB32_original_cap_barrier_full_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:47:15.427625+00:00
-- url     : https://prove2.me/submissions/dcfafad5-fe4d-47bb-93b0-375958e408f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_left_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω, Continuous (fun t : ℝ≥0 => barrierStrategy X c c t ω) := by 
  intro ω
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (continuousWithinAt_univ _ t).mp
  rw [← Set.Iic_union_Ici]
  exact (barrierStrategy_left_continuous X c ω t).union
    (barrierStrategy_right_continuous X c ω t)
