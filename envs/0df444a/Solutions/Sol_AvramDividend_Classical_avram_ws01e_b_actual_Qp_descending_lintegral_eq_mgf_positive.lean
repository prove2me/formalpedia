-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:55:17.558468+00:00
-- url     : https://prove2.me/submissions/3fa0ca59-b17a-422e-9167-3920ab029d66

import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (β : ℝ) (hβ : 0 < β) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    ENNReal.ofReal
      (mgf (fun z : Ω × ℝ =>
        -(runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1))
        ((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) β) := by
  let μ : Measure (Ω × ℝ) :=
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
  let Y : Ω × ℝ → ℝ := fun z =>
    -(runningSup X (Real.toNNReal z.2) z.1 -
      X.X (Real.toNNReal z.2) z.1)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
      X θ p hθ hp hJoint
  have hYMeas : Measurable Y := by
    change Measurable (fun z : Ω × ℝ =>
      -(runningSup X (Real.toNNReal z.2) z.1 -
        X.X (Real.toNNReal z.2) z.1))
    exact (levy_exponential_real_clock_extrema_drawdown_measurable X).snd.neg
  have hYNonpos : ∀ z : Ω × ℝ, Y z ≤ 0 := by
    intro z
    change -(runningSup X (Real.toNNReal z.2) z.1 -
      X.X (Real.toNNReal z.2) z.1) ≤ 0
    exact neg_nonpos.mpr (sub_nonneg.mpr
      ((runningSup_monotone_and_path_le X z.1).2 (Real.toNNReal z.2)))
  have hMeas : Measurable (fun z : Ω × ℝ => Real.exp (β * Y z)) :=
    (measurable_const.mul hYMeas).exp
  have hInt : Integrable (fun z : Ω × ℝ => Real.exp (β * Y z)) μ := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos hβ.le (hYNonpos z))
  have hEq :
      ENNReal.ofReal (∫ z : Ω × ℝ, Real.exp (β * Y z) ∂μ) =
      (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * Y z)) ∂μ) := by
    apply ofReal_integral_eq_lintegral_ofReal hInt
    filter_upwards [] with z
    exact (Real.exp_pos _).le
  simpa only [mgf, Y, μ, mul_neg, neg_mul] using hEq.symm
