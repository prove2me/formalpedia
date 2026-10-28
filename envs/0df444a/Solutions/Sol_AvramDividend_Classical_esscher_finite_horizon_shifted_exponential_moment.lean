-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_horizon_shifted_exponential_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:14:13.672244+00:00
-- url     : https://prove2.me/submissions/cb279af9-ec2c-42b7-85b5-97006ec85ae0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

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
    (t : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    (∫ ω, Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ) *
      Real.exp (η * X.X t ω) ∂P) =
    Real.exp ((t : ℝ) * (X.ψ (θ + η) - X.ψ θ)) := by
  have hsum : 0 ≤ θ + η := add_nonneg hθ hη
  have hLap := (X.laplace t (θ + η) hsum).2
  calc
    (∫ ω, Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ) *
      Real.exp (η * X.X t ω) ∂P) =
      (∫ ω, Real.exp (-(t : ℝ) * X.ψ θ) *
        Real.exp ((θ + η) * X.X t ω) ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-(t : ℝ) * X.ψ θ) *
        ∫ ω, Real.exp ((θ + η) * X.X t ω) ∂P :=
      integral_const_mul _ _
    _ = Real.exp ((t : ℝ) * (X.ψ (θ + η) - X.ψ θ)) := by
      rw [hLap, ← Real.exp_add]
      congr 1
      change -(t : ℝ) * X.ψ θ + (t : ℝ) * X.ψ (θ + η) =
        (t : ℝ) * (X.ψ (θ + η) - X.ψ θ)
      ring
