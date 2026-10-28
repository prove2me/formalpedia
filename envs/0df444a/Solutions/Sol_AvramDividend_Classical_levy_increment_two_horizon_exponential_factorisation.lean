-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_two_horizon_exponential_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:07:53.463358+00:00
-- url     : https://prove2.me/submissions/28ebe2ae-e2d3-4ea2-9ec9-a66ffff18678

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The exponential of a two-horizon Lévy increment factors pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (h k : ℝ≥0) (θ : ℝ) (ω : Ω) :
    Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω)) =
      Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω + h) ω)) *
        Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) := by
  rw [← Real.exp_add]
  congr 1
  ring
