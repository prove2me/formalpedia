-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_discounted_increment_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:08:01.296031+00:00
-- url     : https://prove2.me/submissions/94dc282b-3afd-4bd6-b9a2-55869d553ac6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_memLp_two
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Discounted future Lévy exponential increments are square-integrable after bounded stopping. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) 2 P := by
  have hg := levy_bounded_stopping_increment_exp_memLp_two
    X τ hτ T hbounded h θ hθ
  exact hg.const_mul (Real.exp (-(q * (h : ℝ))))
