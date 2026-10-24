-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_uniform_record_grid_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:48:43.778813+00:00
-- url     : https://prove2.me/submissions/263ad48e-8006-4b71-9e67-e44c8556dccd

import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! Strict first-upcrossing clocks are monotone along every nonnegative equal-spaced record grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (b h : ℝ) (hh : 0 ≤ h) :
    Monotone (fun n : ℕ =>
      ⨅ (r : ℝ≥0) (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) := by
  intro i j hij
  have hir : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hm := mul_le_mul_of_nonneg_right hir hh
  exact firstUpcrossing_threshold_iInf_mono X ω _ _ (add_le_add_right hm b)
