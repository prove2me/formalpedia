-- Prove2me | solution 1 for AvramDividend.Classical.esscher_terminal_clock_indepFun_all_path_functionals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:05:28.174021+00:00
-- url     : https://prove2.me/submissions/baa37a5b-56ca-4082-b5bf-8add0a4c5e02

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Every measurable path functional and the independent exponential clock
are independent under the actual finite-terminal Esscher product law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (p : ℝ) (hp : 0 < p)
    {α : Type*} [MeasurableSpace α]
    (f : Ω → α) (hf : Measurable f) :
    IndepFun (fun z : Ω × ℝ => f z.1)
      (fun z : Ω × ℝ => z.2)
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod
          (expMeasure p)) := by
  haveI : IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  haveI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  exact indepFun_prod hf measurable_id
