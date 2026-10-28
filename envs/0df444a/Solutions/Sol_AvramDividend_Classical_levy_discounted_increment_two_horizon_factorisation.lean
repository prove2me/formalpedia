-- Prove2me | solution 1 for AvramDividend.Classical.levy_discounted_increment_two_horizon_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:11:53.809027+00:00
-- url     : https://prove2.me/submissions/d92d0e64-a72b-415e-9af5-699df19e0f8c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Discounted exponential increments factor through the intermediate horizon pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (h k : ℝ≥0) (θ q : ℝ) (ω : Ω) :
    Real.exp (-(q * ((h + k) : ℝ))) *
      Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω)) =
      (Real.exp (-(q * (h : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) *
        (Real.exp (-(q * (k : ℝ))) *
        Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω + h) ω))) := by
  simp only [← Real.exp_add, NNReal.coe_add]
  congr 1
  ring
