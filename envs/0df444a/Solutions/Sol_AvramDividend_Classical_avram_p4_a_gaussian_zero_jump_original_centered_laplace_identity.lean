-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:21:26.556038+00:00
-- url     : https://prove2.me/submissions/47ea9115-d860-4e4a-aa65-f3e959cd2a9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original zero-jump Levy process has the centred Gaussian Laplace
identity at each deterministic time, directly from the source triplet.
This does not construct a Brownian process or a stochastic integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * (Y.X t ω - (t : ℝ) * Y.c)) ∂P) =
      Real.exp ((t : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) := by
  have hLap := (Y.laplace t θ hθ).2
  calc
    _ = ∫ ω, Real.exp (-θ * (t : ℝ) * Y.c) *
        Real.exp (θ * Y.X t ω) ∂P := by
          congr 1
          funext ω
          rw [← Real.exp_add]
          congr 1
          ring
    _ = Real.exp (-θ * (t : ℝ) * Y.c) *
        (∫ ω, Real.exp (θ * Y.X t ω) ∂P) := by
          rw [integral_const_mul]
    _ = Real.exp ((t : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) := by
          rw [hLap, ← Real.exp_add]
          congr 1
          simp [laplaceExponent, hν]
          ring
