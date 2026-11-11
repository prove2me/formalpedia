-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compound_driver_all_marks_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:46:54.667062+00:00
-- url     : https://prove2.me/submissions/881d63a4-bc40-4cc2-b6c9-55d25ccb002b

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_marks_negative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- A single full-measure event makes every driver jump negative. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω < 0 := by
  exact (MeasureTheory.ae_all_iff).2
    (AvramDividend.Classical.avram_a06_compound_driver_marks_negative hd)