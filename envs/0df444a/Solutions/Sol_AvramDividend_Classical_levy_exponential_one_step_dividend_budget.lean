-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_one_step_dividend_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:36:21.28995+00:00
-- url     : https://prove2.me/submissions/67560153-40ea-4ad5-a09b-c45f9528e23c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
import Theorems.Thm_AvramDividend_Classical_exp_dividend_secant_bound
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
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ q u a : ℝ)
    (hθ : 1 ≤ θ) (ha : 0 ≤ a) (hua : a ≤ u)
    (hψ : X.ψ θ ≤ q) :
    a + Real.exp (-(t : ℝ) * q) *
        (∫ ω, Real.exp (θ * (u - a + X.X t ω)) ∂P) ≤
      Real.exp (θ * u) := by
  have hθ0 : 0 ≤ θ := by linarith
  change laplaceExponent X.c X.σ X.ν θ ≤ q at hψ
  have ht : 0 ≤ (t : ℝ) := by positivity
  have htime :
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ ≤ (t : ℝ) * q :=
    mul_le_mul_of_nonneg_left hψ ht
  have hmult :
      Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ -
        (t : ℝ) * q) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (sub_nonpos.mpr htime)
    simpa using h
  have hs := exp_dividend_secant_bound θ u a hθ ha hua
  calc
    a + Real.exp (-(t : ℝ) * q) *
        (∫ ω, Real.exp (θ * (u - a + X.X t ω)) ∂P) =
      a + Real.exp (θ * (u - a)) *
        Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ -
          (t : ℝ) * q) := by
      rw [levy_transition_exponential_eigenfunction X t θ hθ0 (u - a)]
      have hpair :
          Real.exp (-(t : ℝ) * q) *
              Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ) =
            Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ -
              (t : ℝ) * q) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        a + Real.exp (-(t : ℝ) * q) *
            (Real.exp (θ * (u - a)) *
              Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) =
          a + Real.exp (θ * (u - a)) *
            (Real.exp (-(t : ℝ) * q) *
              Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) := by ring
        _ = _ := by rw [hpair]
    _ ≤ a + Real.exp (θ * (u - a)) := by
      have hm := mul_le_mul_of_nonneg_left hmult
        (Real.exp_nonneg (θ * (u - a)))
      nlinarith
    _ ≤ Real.exp (θ * u) := by linarith