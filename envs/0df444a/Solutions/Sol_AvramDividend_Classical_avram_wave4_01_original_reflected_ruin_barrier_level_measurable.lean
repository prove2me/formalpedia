-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_reflected_ruin_barrier_level_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:48:58.057333+00:00
-- url     : https://prove2.me/submissions/6c14ae7d-843b-4741-8ece-8cc1051a8b33

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The true strict drawdown-ruin clock is Borel in its barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Measurable (fun a : ℝ => barrierRuinTime X a ω) := by
  have hmono : Monotone (fun a : ℝ => barrierRuinTime X a ω) :=
    fun a b hab => barrierRuinTime_mono_barrier X a b hab ω
  exact hmono.measurable
