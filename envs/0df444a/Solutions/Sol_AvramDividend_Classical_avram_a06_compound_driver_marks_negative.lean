-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compound_driver_marks_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:29:32.568666+00:00
-- url     : https://prove2.me/submissions/4bb601ed-fe3e-4c30-af3d-5a2ad6613d75

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- A compound-Poisson driver with a law supported on negative marks
has a.s. negative marks in each coordinate. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ n, ∀ᵐ ω ∂P, Y n ω < 0 := by
  intro n
  have hmeas : Measurable (Y n) := hd.measurable_mark n
  have hnonneg : P (Y n ⁻¹' Ici (0 : ℝ)) = 0 := by
    calc
      P (Y n ⁻¹' Ici (0 : ℝ)) = (Measure.map (Y n) P) (Ici (0 : ℝ)) :=
        (Measure.map_apply hmeas measurableSet_Ici).symm
      _ = ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) (Ici 0) := by
        rw [(hd.law_mark n).map_eq]
      _ = 0 := AvramDividend.Classical.avram_a06_uniform_negative_mark_measure_facts.1
  exact (ae_iff).2 (by simpa only [Set.preimage, Set.mem_setOf_eq, Set.mem_Ici, not_lt] using hnonneg)