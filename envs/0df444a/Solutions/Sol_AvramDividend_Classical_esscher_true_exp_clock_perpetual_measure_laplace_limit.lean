-- Prove2me | solution 1 for AvramDividend.Classical.esscher_true_exp_clock_perpetual_measure_laplace_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T21:56:47.808845+00:00
-- url     : https://prove2.me/submissions/d1df49b4-16a5-4f3b-973a-514bd73a4799

import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_true_exp_clock_perpetual_laplace_limit
import Theorems.Thm_AvramDividend_Classical_esscher_probability_weighted_cdf_real_eq_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_true_random_clock_reflected_law_probability
import Theorems.Thm_AvramDividend_Classical_esscher_true_real_clock_reflected_law_nonnegative_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

/-- The genuine Esscher random-clock reflected-infimum Laplace transforms
    converge to the canonical supported perpetual probability law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ν (Iio (0 : ℝ)) = 0 ∧
      ∀ β : ℝ, 0 < β →
        Tendsto (fun n : ℕ =>
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂
            (Measure.map (fun z : Ω × ℝ =>
              -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ Real.toNNReal z.2 ∧
                y = X.X s z.1})
              ((P.prod (expMeasure (p n))).withDensity
                (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
                  (φ * X.X (Real.toNNReal z.2) z.1 -
                    (Real.toNNReal z.2 : ℝ) * X.ψ φ)))))))
          atTop (nhds (∫⁻ z : ℝ,
            ENNReal.ofReal (Real.exp (-β * z)) ∂ν)) := by
  obtain ⟨ν, hνP, hν0, hweighted⟩ :=
    esscher_true_exp_clock_perpetual_laplace_limit X q φ hq hφ hroot p hp hpos
  letI : IsProbabilityMeasure ν := hνP
  set μ : ℕ → Measure ℝ := fun n =>
    Measure.map (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ Real.toNNReal z.2 ∧
        y = X.X s z.1})
      ((P.prod (expMeasure (p n))).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) with hμ
  have hμP (n : ℕ) : IsProbabilityMeasure (μ n) := by
    exact esscher_true_random_clock_reflected_law_probability
      X φ (p n) hφ.le (hpos n)
  have hμ0 (n : ℕ) : μ n (Iio (0 : ℝ)) = 0 :=
    esscher_true_real_clock_reflected_law_nonnegative_support X _
  refine ⟨ν, hνP, hν0, fun β hβ => ?_⟩
  have hCDF : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * cdf (μ n) x ∂volume))
      atTop (nhds (ENNReal.ofReal (1 / β) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν))) := by
    simpa only [μ] using hweighted β hβ
  have hid (n : ℕ) :
      ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * cdf (μ n) x ∂volume) =
      ENNReal.ofReal (1 / β) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂(μ n)) := by
    letI : IsProbabilityMeasure (μ n) := hμP n
    exact esscher_probability_weighted_cdf_real_eq_laplace
      (μ n) (hμ0 n) β hβ
  have hscaled : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (1 / β) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂(μ n)))
      atTop (nhds (ENNReal.ofReal (1 / β) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν))) := by
    have heq : (fun n : ℕ =>
        ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
          Real.exp (-β * x) * cdf (μ n) x ∂volume)) =
        (fun n : ℕ => ENNReal.ofReal (1 / β) *
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂(μ n))) :=
      funext hid
    rwa [heq] at hCDF
  have hcancel :
      ENNReal.ofReal β * ENNReal.ofReal (1 / β) = 1 := by
    rw [← ENNReal.ofReal_mul hβ.le]
    have hreal : β * (1 / β) = (1 : ℝ) := by
      field_simp [ne_of_gt hβ]
    rw [hreal]
    simp
  have hscaled' := ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal β) hscaled (Or.inr (by simp))
  simpa only [μ, ← mul_assoc, hcancel, one_mul] using hscaled'
