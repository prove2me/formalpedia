-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_drift_deficit_increment_exp_gap_expectation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:36:02.73549+00:00
-- url     : https://prove2.me/submissions/fba6cf45-4206-4e10-9ed4-3624f53be88a

import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Theorems.Thm_AvramDividend_Classical_bv_actual_discounted_deficit_exp_gap_expectation
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ ω, (1 : ℝ) -
      Real.exp (-θ * ((X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω))) ∂P) =
      1 - Real.exp (-(((t - s : ℝ≥0) : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)) := by
  have hid := actual_levy_drift_deficit_stationary_increment_law X s t hst
  have hφ : Measurable (fun z : ℝ => (1 : ℝ) - Real.exp (-θ * z)) := by fun_prop
  have e1 := (hid.comp hφ).integral_eq
  simp only [Function.comp_def] at e1
  rw [e1, ← bv_actual_discounted_deficit_exp_gap_expectation X hBV (t - s) θ hθ]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp only
  rw [← Real.exp_add]
  congr 2
  ring
