-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_integrator_new_given_perpetual_cdf_true_joint_laplace_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:00:48.763978+00:00
-- url     : https://prove2.me/submissions/0c4484e6-2f3b-4eaf-92fc-8a6eaf75fdc5

import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_true_joint_clock_cdf_tendsto_perpetual
import Theorems.Thm_AvramDividend_Classical_esscher_probability_cdf_limits_imply_weighted_laplace_limits
import Theorems.Thm_AvramDividend_Classical_esscher_probability_weighted_cdf_real_eq_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_true_random_clock_reflected_law_probability
import Theorems.Thm_AvramDividend_Classical_esscher_true_real_clock_reflected_law_nonnegative_support
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

/-- Genuine finite-clock Laplace convergence to an explicitly supplied
canonical CDF law; the ν is not an independently chosen existential witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (ν : Measure ℝ) (hνP : IsProbabilityMeasure ν)
    (hν0 : ν (Iio (0 : ℝ)) = 0)
    (hνCDF : ∀ x : ℝ, ν (Iic x) =
      (⨅ t : ℝ≥0, ENNReal.ofReal
        (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (θ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∀ β : ℝ, 0 < β →
      Tendsto (fun n : ℕ =>
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂
          (Measure.map (fun z : Ω × ℝ =>
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})
            ((P.prod (expMeasure (p n))).withDensity
              (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
                (θ * X.X (Real.toNNReal z.2) z.1 -
                  (Real.toNNReal z.2 : ℝ) * X.ψ θ)))))))
        atTop (nhds (∫⁻ z : ℝ,
          ENNReal.ofReal (Real.exp (-β * z)) ∂ν)) := by
  letI : IsProbabilityMeasure ν := hνP
  let μ : ℕ → Measure ℝ := fun n =>
    Measure.map (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ Real.toNNReal z.2 ∧
        y = X.X s z.1})
      ((P.prod (expMeasure (p n))).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
  have ht : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) :=
    measurable_real_toNNReal.comp measurable_snd
  have hR : Measurable (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) :=
    (levy_running_infimum_joint_time_path_measurable X).comp
      (ht.prodMk measurable_fst)
  have hμP (n : ℕ) : IsProbabilityMeasure (μ n) :=
    esscher_true_random_clock_reflected_law_probability
      X θ (p n) hθ (hpos n)
  have hμ0 (n : ℕ) : μ n (Iio (0 : ℝ)) = 0 :=
    esscher_true_real_clock_reflected_law_nonnegative_support X _
  have hCDF (x : ℝ) :
      Tendsto (fun n : ℕ => μ n (Iic x))
        atTop (nhds (ν (Iic x))) := by
    have h := esscher_true_joint_clock_cdf_tendsto_perpetual
      X θ hθ x ν (hνCDF x) p hp hpos
    convert h using 1
    funext n
    rw [Measure.map_apply hR measurableSet_Iic]
    rfl
  intro β hβ
  have hreal :=
    esscher_probability_cdf_limits_imply_weighted_laplace_limits
      μ ν hμP hCDF β hβ
  have hCDFLap : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * cdf (μ n) x ∂volume))
      atTop (nhds (ENNReal.ofReal (1 / β) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν))) := by
    have hE := (ENNReal.continuous_ofReal.tendsto
      (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * cdf ν x ∂volume)).comp hreal
    have hTarget := esscher_probability_weighted_cdf_real_eq_laplace
      ν hν0 β hβ
    rw [hTarget] at hE
    exact hE
  have hid (n : ℕ) :
      ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * cdf (μ n) x ∂volume) =
      ENNReal.ofReal (1 / β) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂(μ n)) := by
    letI : IsProbabilityMeasure (μ n) := hμP n
    exact esscher_probability_weighted_cdf_real_eq_laplace
      (μ n) (hμ0 n) β hβ
  have hscaled : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / β) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂(μ n)))
      atTop (nhds (ENNReal.ofReal (1 / β) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν))) := by
    have heq : (fun n : ℕ =>
        ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
          Real.exp (-β * x) * cdf (μ n) x ∂volume)) =
        (fun n : ℕ => ENNReal.ofReal (1 / β) *
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂(μ n))) :=
      funext hid
    rwa [heq] at hCDFLap
  have hcancel : ENNReal.ofReal β * ENNReal.ofReal (1 / β) = 1 := by
    rw [← ENNReal.ofReal_mul hβ.le]
    have hr : β * (1 / β) = (1 : ℝ) := by
      field_simp [ne_of_gt hβ]
    rw [hr]
    simp
  have hscaled' := ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal β) hscaled (Or.inr (by simp))
  simpa only [μ, ← mul_assoc, hcancel, one_mul] using hscaled'