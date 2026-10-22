-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_exponential_generator_deriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:41:37.377495+00:00
-- url     : https://prove2.me/submissions/565ecc6e-37c6-46d6-871c-cd97d67814da

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi
import Theorems.Thm_AvramDividend_Classical_levy_exponential_semigroup_multiplier_deriv_zero
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ x : ℝ) :
    HasDerivAt
      (fun h : ℝ =>
        Real.exp (θ * x) *
          Real.exp (h * laplaceExponent X.c X.σ X.ν θ))
      (X.generator (fun z : ℝ => Real.exp (θ * z)) x)
      0 := by
  rw [generator_exp_eq_psi X θ x]
  change HasDerivAt
    (fun h : ℝ =>
      Real.exp (θ * x) *
        Real.exp (h * laplaceExponent X.c X.σ X.ν θ))
    (Real.exp (θ * x) * laplaceExponent X.c X.σ X.ν θ)
    0
  exact levy_exponential_semigroup_multiplier_deriv_zero X θ x
