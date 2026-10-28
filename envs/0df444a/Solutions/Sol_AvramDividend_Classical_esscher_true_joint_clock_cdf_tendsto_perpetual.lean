-- Prove2me | solution 1 for AvramDividend.Classical.esscher_true_joint_clock_cdf_tendsto_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:48:24.711333+00:00
-- url     : https://prove2.me/submissions/75bd4617-5012-4b20-a8ea-71434f08624c

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_esscher_joint_exp_clock_reflected_cdf_mixture
import Theorems.Thm_AvramDividend_Classical_esscher_clock_finite_cdf_equals_survival_mix
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_probability_real_lintegral_bridge
import Theorems.Thm_AvramDividend_Classical_esscher_true_clock_survival_cdf_to_real_iInf
import Theorems.Thm_AvramDividend_Classical_esscher_ofReal_antitone_iInf_bridge
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_tendsto_iInf
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

/-- True random-horizon Esscher CDF tends to its canonical perpetual CDF. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (ν : Measure ℝ)
    (hν : ν (Iic x) = (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    Tendsto (fun n : ℕ =>
      ((P.prod (expMeasure (p n))).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
        {z : Ω × ℝ | -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x})
      atTop (nhds (ν (Iic x))) := by
  let F : ℝ≥0 → ℝ := fun t => (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
  have hanti : Antitone F := by
    intro t u htu
    exact esscher_weighted_lower_survival_mass_antitone X θ hθ x t u htu
  have hlimF : Tendsto F atTop (nhds (⨅ t : ℝ≥0, F t)) :=
    esscher_weighted_lower_survival_mass_tendsto_iInf X θ hθ x
  have hInf : (⨅ t : ℝ≥0, ENNReal.ofReal (F t)) =
      ENNReal.ofReal (⨅ t : ℝ≥0, F t) :=
    esscher_ofReal_antitone_iInf_bridge F _ hanti hlimF
  have hmeas : Measurable (fun v : ℝ => F (Real.toNNReal v)) :=
    hanti.measurable.comp measurable_real_toNNReal
  have h0 (v : ℝ) : 0 ≤ F (Real.toNNReal v) :=
    (esscher_weighted_lower_survival_mass_unit_interval X θ hθ x (Real.toNNReal v)).1
  have h1 (v : ℝ) : F (Real.toNNReal v) ≤ 1 :=
    (esscher_weighted_lower_survival_mass_unit_interval X θ hθ x (Real.toNNReal v)).2
  have hjoint (n : ℕ) :
      ((P.prod (expMeasure (p n))).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ | -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x} =
      ENNReal.ofReal (∫ v : ℝ, F (Real.toNNReal v) ∂expMeasure (p n)) := by
    calc
      _ = (∫⁻ v : ℝ, (P.withDensity
        (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal v) ω -
          (Real.toNNReal v : ℝ) * X.ψ θ))))
        {ω : Ω | -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal v ∧ y = X.X s ω} ≤ x}
        ∂expMeasure (p n)) :=
        esscher_joint_exp_clock_reflected_cdf_mixture X θ (p n) x hθ (hpos n)
      _ = (∫⁻ v : ℝ, ENNReal.ofReal (F (Real.toNNReal v))
          ∂expMeasure (p n)) := by
        exact esscher_clock_finite_cdf_equals_survival_mix X θ (p n) x hθ (hpos n)
      _ = _ := by
        letI : IsProbabilityMeasure (expMeasure (p n)) :=
          isProbabilityMeasure_expMeasure (hpos n)
        exact esscher_bounded_probability_real_lintegral_bridge
          (expMeasure (p n)) (fun v => F (Real.toNNReal v)) hmeas h0 h1
  have hreal : Tendsto (fun n : ℕ => (∫ v : ℝ, F (Real.toNNReal v) ∂expMeasure (p n)))
      atTop (nhds (⨅ t : ℝ≥0, F t)) :=
    esscher_true_clock_survival_cdf_to_real_iInf X θ hθ x p hp hpos
  have hnonneg := (ENNReal.continuous_ofReal.tendsto
    (⨅ t : ℝ≥0, F t)).comp hreal
  have hfun :
      (fun n : ℕ => ((P.prod (expMeasure (p n))).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ | -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x}) =
      (fun n : ℕ => ENNReal.ofReal (∫ v : ℝ, F (Real.toNNReal v) ∂expMeasure (p n))) := by
    funext n
    exact hjoint n
  rw [hfun, hν, hInf]
  exact hnonneg
