-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:11:23.112254+00:00
-- url     : https://prove2.me/submissions/585666f6-bcfa-44d4-8baa-46d4ae02fab2

import Mathlib.Probability.Moments.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The original independent exponential-clock drawdown Laplace integral
is exactly the real MGF evaluated at positive arguments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (β : ℝ) (hβ : 0 < β) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (expMeasure p))) =
    ENNReal.ofReal
      (mgf (fun z : Ω × ℝ =>
        -(runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1))
        (P.prod (expMeasure p)) β) := by
  have hψ0 : X.ψ 0 = 0 := levy_laplace_exponent_zero X
  have hJoint : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        ((0 : ℝ) * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ 0))) := by
    simpa [hψ0] using
      (measurable_const : Measurable (fun _ : Ω × ℝ => (1 : ℝ≥0∞)))
  have h := avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
    X 0 p le_rfl hp hJoint β hβ
  have hdensity :
      (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
        ((0 : ℝ) * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ 0))) =
      (1 : Ω × ℝ → ℝ≥0∞) := by
    funext z
    simp [hψ0]
  have hmeasure :
      (P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          ((0 : ℝ) * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ 0))) =
      P.prod (expMeasure p) := by
    rw [hdensity, withDensity_one]
  rw [hmeasure] at h
  exact h
