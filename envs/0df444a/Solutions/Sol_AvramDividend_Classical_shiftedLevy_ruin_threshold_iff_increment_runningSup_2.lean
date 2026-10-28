-- Prove2me | solution 2 for AvramDividend.Classical.shiftedLevy_ruin_threshold_iff_increment_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:50:32.896463+00:00
-- url     : https://prove2.me/submissions/ca54bddd-e1e9-491c-891e-80a51ad6a4c1

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_runningSup_nonnegative
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
  obtain ⟨M, hM⟩ := levyPath_bddAbove_Icc X ω (u + t)
  have hb : BddAbove ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hM ⟨u + v, ⟨zero_le, add_le_add_right hv.2 u⟩, rfl⟩
  have he := shiftedSup_increment_eq_sup_sub (fun r => X.X r ω) u t hb
  have hn := shiftedLevy_runningSup_nonnegative X ω u t
  rw [← he, max_eq_right hn]
