-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_genuine_tilted_clock_descending_mgf_analytic_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:57:25.524995+00:00
-- url     : https://prove2.me/submissions/18e2e0b1-d3cb-4601-8681-ec651831dc94

import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Closure
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
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    AnalyticOnNhd ℝ
      (mgf
        (fun z : Ω × ℝ =>
          -(runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1))
        ((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ θ)))))
      (Set.Ioi 0) := by
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
  have hExpInt : ∀ β : ℝ, 0 < β →
      Integrable (fun z : Ω × ℝ => Real.exp (β * Y z)) μ := by
    intro β hβ
    have hMeas : Measurable
        (fun z : Ω × ℝ => Real.exp (β * Y z)) :=
      (measurable_const.mul hYMeas).exp
    apply Integrable.of_bound hMeas.aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos hβ.le (hYNonpos z))
  have hSubset : (Set.Ioi (0 : ℝ)) ⊆ integrableExpSet Y μ := by
    intro β hβ
    exact hExpInt β hβ
  have hInterior : Set.Ioi (0 : ℝ) ⊆
      interior (integrableExpSet Y μ) :=
    isOpen_Ioi.subset_interior_iff.mpr hSubset
  simpa only [Y, μ] using
    (analyticOnNhd_mgf (X := Y) (μ := μ)).mono hInterior
