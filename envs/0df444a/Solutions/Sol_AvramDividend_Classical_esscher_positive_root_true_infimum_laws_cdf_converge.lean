-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_true_infimum_laws_cdf_converge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T19:35:54.462987+00:00
-- url     : https://prove2.me/submissions/f0addf23-16b1-4055-95f3-e8b997bc29c7

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_genuine_exponential_cdf_perpetual_measure
import Theorems.Thm_AvramDividend_Classical_esscher_true_random_clock_reflected_law_probability
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

/-- The genuine reflected-infimum pushforward probability laws converge in every CDF. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ n : ℕ, IsProbabilityMeasure (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) ((P.prod (expMeasure (p n))).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ)))))) ∧
      (∀ x : ℝ, Tendsto (fun n : ℕ => (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) ((P.prod (expMeasure (p n))).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) (Iic x))
         atTop (nhds (ν (Iic x)))) ∧
      (∀ b : ℝ, 0 < b →
        ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b)) ≤ ν (Iic b)) := by
  obtain ⟨ν, hprobν, hCDF, hlower⟩ :=
    esscher_positive_root_genuine_exponential_cdf_perpetual_measure
      X q φ hq hφ hroot p hp hpos
  have ht : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) :=
    measurable_real_toNNReal.comp measurable_snd
  have hR : Measurable (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) :=
    (levy_running_infimum_joint_time_path_measurable X).comp
      (ht.prodMk measurable_fst)
  refine ⟨ν, hprobν, ?_, ?_, hlower⟩
  · intro n
    exact esscher_true_random_clock_reflected_law_probability
      X φ (p n) (le_of_lt hφ) (hpos n)
  · intro x
    convert hCDF x using 1
    funext n
    rw [Measure.map_apply hR measurableSet_Iic]
    rfl
