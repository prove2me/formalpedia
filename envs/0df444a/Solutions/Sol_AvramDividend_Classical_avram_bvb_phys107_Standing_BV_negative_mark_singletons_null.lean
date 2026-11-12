-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:20:31.452414+00:00
-- url     : https://prove2.me/submissions/e3ab0970-708e-4bd1-9e22-083c9566af32

import Mathlib
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- Under the original bounded-variation standing assumptions, no
negative mark, including a state-dependent ruin threshold, has an atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (z : ℝ) : X.ν ({z} : Set ℝ) = 0 := by
  have hνac : X.ν ≪ (volume : Measure ℝ) :=
    standing_bv_levy_absolutely_continuous X hStanding hBV
  apply hνac
  simp
