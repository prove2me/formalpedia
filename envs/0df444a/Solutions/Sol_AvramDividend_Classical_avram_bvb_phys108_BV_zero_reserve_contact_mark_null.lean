-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys108_BV_zero_reserve_contact_mark_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:29:53.087634+00:00
-- url     : https://prove2.me/submissions/f0badd38-3069-42e3-86c5-195397eabb3e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- Under the original Standing and BV hypotheses, the jump mark
which brings reserve `a` exactly to zero has zero Lévy mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (a : ℝ) : X.ν {z : ℝ | a + z = 0} = 0 := by
  have hset : {z : ℝ | a + z = 0} = ({-a} : Set ℝ) := by
    ext z
    constructor
    · intro hz
      change a + z = 0 at hz
      simp only [Set.mem_singleton_iff]
      linarith
    · intro hz
      simp only [Set.mem_singleton_iff] at hz
      change a + z = 0
      rw [hz]
      ring
  rw [hset]
  exact avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
    X hStanding hBV (-a)
