-- Prove2me | solution 1 for AvramDividend.Classical.shiftedLevy_ruin_threshold_iff_increment_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:49:20.215085+00:00
-- url     : https://prove2.me/submissions/355d9f83-164e-40d4-9201-a371503958d1

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_runningSup_nonnegative
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ω : Ω) (u t : ℝ≥0) :
    (a + (X.X (u + t) ω - X.X u ω) <
      max 0
        (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X u ω)) ↔
    (a + (X.X (u + t) ω - X.X u ω) <
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) ''
        Set.Icc 0 t)) := by
  classical
  have hb :
      BddAbove ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) := by
    rcases levyPath_bddAbove_Icc X ω (u + t) with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact hK (Set.mem_image_of_mem
      (fun r : ℝ≥0 => X.X r ω)
      ⟨bot_le, add_le_add_right hr.2 u⟩)
  have hshift :=
    shiftedSup_increment_eq_sup_sub
      (fun r : ℝ≥0 => X.X r ω) u t hb
  have hpositive :=
    shiftedLevy_runningSup_nonnegative X ω u t
  rw [← hshift, max_eq_right hpositive]
