-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_genuine_exponential_cdf_perpetual_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:52:50.173365+00:00
-- url     : https://prove2.me/submissions/da125899-d2e1-4091-93d5-f7c2c4be27e3

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
import Theorems.Thm_AvramDividend_Classical_esscher_true_joint_clock_cdf_tendsto_perpetual
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

/-- Positive Esscher-root exponential-horizon CDFs converge at every threshold
    to an actual perpetual probability law with proven nondegeneracy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ x : ℝ, Tendsto (fun n : ℕ => ((P.prod (expMeasure (p n))).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (φ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
       {z : Ω × ℝ | -sInf {y : ℝ | ∃ s : ℝ≥0,
         s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x})
        atTop (nhds (ν (Iic x)))) ∧
      (∀ b : ℝ, 0 < b →
        ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b)) ≤ ν (Iic b)) := by
  obtain ⟨ν, hνprob, hνcdf, hνlower⟩ :=
    chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
      X q φ hq hφ hroot
  refine ⟨ν, hνprob, ?_, hνlower⟩
  intro x
  exact esscher_true_joint_clock_cdf_tendsto_perpetual
    X φ (le_of_lt hφ) x ν (hνcdf x) p hp hpos
