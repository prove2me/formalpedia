-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compoundPoisson_one_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:41:12.302187+00:00
-- url     : https://prove2.me/submissions/297324f9-81b6-4d22-ae1b-185bac7c749f

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_negative
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_above_minus_one
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_le_drift
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_ge_drift_minus_count
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_fixedTime_measurable_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- The unit-time compound-Poisson marginal is dominated by one plus
the integrable Poisson jump count, because all jumps lie in (-1,0). -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    Integrable (LevyFoundations.compoundPoisson (1 : ℝ) τ Y 1) P := by
  have hmeas : Measurable (LevyFoundations.compoundPoisson (1 : ℝ) τ Y 1) :=
    AvramDividend.Classical.avram_a06_compoundPoisson_fixedTime_measurable_public
      (1 : ℝ) τ Y hd.measurable_interarrival hd.measurable_mark 1
  have hdom : Integrable (fun ω => (1 : ℝ) +
      (LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival τ n ω) 1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).add
      (AvramDividend.Classical.avram_a06_compound_jumpCount_integrable hd 1)
  refine hdom.mono hmeas.aestronglyMeasurable ?_
  filter_upwards
    [AvramDividend.Classical.avram_a06_compound_driver_all_marks_negative hd,
      AvramDividend.Classical.avram_a06_compound_driver_all_marks_above_minus_one hd]
    with ω hneg habove
  let N := LevyFoundations.jumpCount
    (fun n => LevyFoundations.arrival τ n ω) 1
  let x := LevyFoundations.compoundPoisson (1 : ℝ) τ Y 1 ω
  have hupper : x ≤ (1 : ℝ) := by
    simpa only [x, one_mul] using
      (AvramDividend.Classical.avram_a06_compoundPoisson_path_le_drift
        (1 : ℝ) τ Y ω (fun n => le_of_lt (hneg n)) 1)
  have hlower : (1 : ℝ) - (N : ℝ) ≤ x := by
    simpa only [x, N, one_mul] using
      (AvramDividend.Classical.avram_a06_compoundPoisson_path_ge_drift_minus_count
        (1 : ℝ) τ Y ω (fun n => le_of_lt (habove n)) 1)
  have hn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have habs : |x| ≤ (1 : ℝ) + (N : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hpositive : (0 : ℝ) ≤ (1 : ℝ) + (N : ℝ) := by linarith
  simpa only [x, N, Real.norm_eq_abs, abs_of_nonneg hpositive] using habs
