-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compoundPoisson_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:08:56.335119+00:00
-- url     : https://prove2.me/submissions/e47beab0-3d53-4d20-89b9-41ac78cc9db5

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_negative
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_le_drift
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_fixedTime_measurable_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- The source-exact compound-Poisson exponential has a deterministic
integrable bound at each fixed time and nonnegative Laplace frequency. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (t θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable
      (fun ω => Real.exp (θ * LevyFoundations.compoundPoisson (1 : ℝ) τ Y t ω)) P := by
  have hmeas : Measurable
      (fun ω => Real.exp (θ * LevyFoundations.compoundPoisson (1 : ℝ) τ Y t ω)) := by
    exact Real.measurable_exp.comp
      (measurable_const.mul
        (AvramDividend.Classical.avram_a06_compoundPoisson_fixedTime_measurable_public
          (1 : ℝ) τ Y hd.measurable_interarrival hd.measurable_mark t))
  refine (integrable_const (Real.exp (θ * t)) : Integrable
    (fun _ : Ω => Real.exp (θ * t)) P).mono hmeas.aestronglyMeasurable ?_
  filter_upwards [AvramDividend.Classical.avram_a06_compound_driver_all_marks_negative hd]
    with ω hneg
  have hb := AvramDividend.Classical.avram_a06_compoundPoisson_path_le_drift
    (1 : ℝ) τ Y ω (fun n => le_of_lt (hneg n)) t
  have hmul := mul_le_mul_of_nonneg_left hb hθ
  have hexp : Real.exp (θ * LevyFoundations.compoundPoisson (1 : ℝ) τ Y t ω) ≤
      Real.exp (θ * t) :=
    Real.exp_le_exp.mpr (by simpa only [one_mul] using hmul)
  have hpL : 0 ≤ Real.exp (θ * LevyFoundations.compoundPoisson (1 : ℝ) τ Y t ω) :=
    (Real.exp_pos _).le
  have hpR : 0 ≤ Real.exp (θ * t) := (Real.exp_pos _).le
  simpa only [Real.norm_eq_abs, abs_of_nonneg hpL, abs_of_nonneg hpR] using hexp
