-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compound_driver_all_marks_above_minus_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:16:50.730193+00:00
-- url     : https://prove2.me/submissions/82fc60ce-52d0-41c5-8fc5-388cef2efef5

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- The canonical uniform negative-mark law gives one common event on which
every jump lies above -1, enabling an L1 jump-count envelope. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ n, -1 < Y n ω := by
  have hbad : ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))
      (Iic (-1 : ℝ)) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iic]
    have hs : Iic (-1 : ℝ) ∩ Ioo (-1 : ℝ) 0 = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false]
      intro hy
      exact (not_lt_of_ge hy.1) hy.2.1
    simp [hs]
  apply (MeasureTheory.ae_all_iff).2
  intro n
  have hmeas : Measurable (Y n) := hd.measurable_mark n
  have hzero : P (Y n ⁻¹' Iic (-1 : ℝ)) = 0 := by
    calc
      P (Y n ⁻¹' Iic (-1 : ℝ)) = (Measure.map (Y n) P) (Iic (-1 : ℝ)) :=
        (Measure.map_apply hmeas measurableSet_Iic).symm
      _ = ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) (Iic (-1 : ℝ)) := by
        rw [(hd.law_mark n).map_eq]
      _ = 0 := hbad
  exact (ae_iff).2 (by
    simpa only [Set.preimage, Set.mem_setOf_eq, Set.mem_Iic, not_lt] using hzero)
