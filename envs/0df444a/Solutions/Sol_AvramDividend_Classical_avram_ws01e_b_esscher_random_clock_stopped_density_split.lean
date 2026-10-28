-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_esscher_random_clock_stopped_density_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:12:08.670004+00:00
-- url     : https://prove2.me/submissions/0e73a85a-ad3a-443a-a72c-61e382f6a88c

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_compensated_exp_time_split
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (τ : Ω → ℝ≥0)
    (e : Θ → ℝ≥0) (ω : Ω) (η : Θ)
    (hObs : τ ω ≤ e η) :
    Real.exp
      (θ * X.X (e η) ω -
        (e η : ℝ) * laplaceExponent X.c X.σ X.ν θ) =
    Real.exp
      (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
    Real.exp
      (θ * (X.X (e η) ω - X.X (τ ω) ω) -
        ((e η - τ ω : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ) := by
  have hs : τ ω + (e η - τ ω) = e η :=
    add_tsub_cancel_of_le hObs
  simpa only [hs] using
    (esscher_compensated_exp_time_split X θ (τ ω) (e η - τ ω) ω)
