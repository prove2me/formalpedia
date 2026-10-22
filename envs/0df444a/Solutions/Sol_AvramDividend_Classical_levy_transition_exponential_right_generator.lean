-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_exponential_right_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:11:07.082709+00:00
-- url     : https://prove2.me/submissions/72caeb72-b907-4035-a3b8-a4a21ad4f120

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
import Theorems.Thm_AvramDividend_Classical_levy_exponential_semigroup_multiplier_deriv_zero
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ * ((∫ ω, Real.exp (θ * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          Real.exp (θ * x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator (fun z : ℝ => Real.exp (θ * z)) x)) := by
  have hlim :
      Tendsto
        (fun h : ℝ =>
          h⁻¹ * (Real.exp (θ * x) *
            Real.exp (h * laplaceExponent X.c X.σ X.ν θ) -
            Real.exp (θ * x)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (Real.exp (θ * x) * laplaceExponent X.c X.σ X.ν θ)) := by
    have hd :=
      (levy_exponential_semigroup_multiplier_deriv_zero X θ x).tendsto_slope_zero_right
    simpa [smul_eq_mul] using hd
  have hEq :
      (fun h : ℝ =>
        h⁻¹ * ((∫ ω, Real.exp (θ * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          Real.exp (θ * x))) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun h : ℝ =>
        h⁻¹ * (Real.exp (θ * x) *
          Real.exp (h * laplaceExponent X.c X.σ X.ν θ) -
          Real.exp (θ * x))) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := Set.mem_Ioi.mp hh
    have hcast : (Real.toNNReal h : ℝ) = h :=
      Real.coe_toNNReal h (le_of_lt hpos)
    rw [levy_transition_exponential_eigenfunction X (Real.toNNReal h) θ hθ x, hcast]
  rw [generator_exp_eq_psi X θ x]
  change Tendsto _ _ (nhds (Real.exp (θ * x) * laplaceExponent X.c X.σ X.ν θ))
  exact hlim.congr' hEq.symm