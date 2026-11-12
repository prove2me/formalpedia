-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_phys108_BV_zero_reserve_contact_mark_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:30:56.301236+00:00
-- url     : https://prove2.me/submissions/43d287f2-173f-4589-bf7e-c12f2802a415

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- A reserve-hitting jump mark is a singleton and has no Levy mass. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (a : ℝ) :
    X.ν {z : ℝ | a + z = 0} = 0 := by
  have hSet : {z : ℝ | a + z = 0} = {(-a)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hz
      linarith
    · intro hz
      subst z
      ring
  rw [hSet]
  exact avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
    X hStanding hBV (-a)
