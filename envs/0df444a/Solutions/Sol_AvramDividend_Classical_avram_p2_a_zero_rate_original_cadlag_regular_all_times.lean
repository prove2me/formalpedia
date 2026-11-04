-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_cadlag_regular_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:11:00.635205+00:00
-- url     : https://prove2.me/submissions/f1b6b7ba-02a6-4bfa-900f-1385ca820938

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.LeftRightNhds
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- The exact original source has the one-sided continuity hypotheses used
by the uniform-grid jump limit, including the vacuous strict-left zero clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    (∀ t : ℝ≥0,
      Tendsto (fun u : ℝ≥0 => X.X u ω) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t))) ∧
    (∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => X.X u ω) (Ici t) t) := by
  constructor
  · intro t
    by_cases ht : 0 < t
    · exact tendsto_leftLim_of_tendsto (X.leftLim ω t ht)
    · have htzero : t = 0 :=
        le_antisymm (le_of_not_gt ht) (zero_le)
      subst t
      simp
  · intro t
    exact X.rightCont ω t
