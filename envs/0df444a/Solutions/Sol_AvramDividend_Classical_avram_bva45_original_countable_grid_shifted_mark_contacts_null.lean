-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva45_original_countable_grid_shifted_mark_contacts_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:00:12.649429+00:00
-- url     : https://prove2.me/submissions/c08593de-6ef5-4fed-b5e8-54a46f80fde4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- Countably many translated reserve-boundary singletons remain null. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (a : ℕ → ℝ) (b : ℝ) :
    X.ν {z : ℝ | ∃ n : ℕ, a n + z = b} = 0 := by
  have hSingle (n : ℕ) : X.ν {z : ℝ | a n + z = b} = 0 := by
    have hSet : {z : ℝ | a n + z = b} = {b - a n} := by
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
      X hStanding hBV (b - a n)
  have hUnion : {z : ℝ | ∃ n : ℕ, a n + z = b} =
      ⋃ n : ℕ, {z : ℝ | a n + z = b} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hUnion]
  exact measure_iUnion_null hSingle
