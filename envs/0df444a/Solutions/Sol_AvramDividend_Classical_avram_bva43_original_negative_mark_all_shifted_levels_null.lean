-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva43_original_negative_mark_all_shifted_levels_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:59:38.239392+00:00
-- url     : https://prove2.me/submissions/71d777e0-ccda-4404-addb-1f8f7498792d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- Shifting a reserve boundary simply translates the null singleton. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (a b : ℝ) :
    X.ν {z : ℝ | a + z = b} = 0 := by
  have hSet : {z : ℝ | a + z = b} = {b - a} := by
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
    X hStanding hBV (b - a)
