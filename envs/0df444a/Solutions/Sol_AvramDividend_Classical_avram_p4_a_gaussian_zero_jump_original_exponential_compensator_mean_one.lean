-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_exponential_compensator_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:58:41.689795+00:00
-- url     : https://prove2.me/submissions/2e0b07e7-5026-48f4-980c-4ae3082d87ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true zero-jump Levy source has unit-mean Gaussian-compensated
centred exponential at every fixed time. This is the expectation
precondition for an exponential martingale, not a conditional expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
       (θ * (Y.X t ω - (t : ℝ) * Y.c) -
         (t : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) ∂P) = 1 := by
  have hLap :=
    avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
      Y hν t θ hθ
  let A : ℝ := (t : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)
  calc
    _ = ∫ ω, Real.exp (-A) *
        Real.exp (θ * (Y.X t ω - (t : ℝ) * Y.c)) ∂P := by
          congr 1
          funext ω
          rw [← Real.exp_add]
          congr 1
          dsimp [A]
          ring
    _ = Real.exp (-A) *
        (∫ ω, Real.exp (θ * (Y.X t ω - (t : ℝ) * Y.c)) ∂P) := by
          rw [integral_const_mul]
    _ = 1 := by
          rw [hLap, ← Real.exp_add]
          simp [A]
