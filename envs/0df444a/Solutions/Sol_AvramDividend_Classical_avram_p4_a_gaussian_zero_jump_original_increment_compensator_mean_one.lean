-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_increment_compensator_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:10:52.679568+00:00
-- url     : https://prove2.me/submissions/e457a2a5-3c8f-4fd1-b3ee-faa18f10410b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original zero-jump Gaussian compensated increment has unit expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
      (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) -
        ((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) ∂P) = 1 := by
  have hLap :=
    avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
      Y hν s t hst θ hθ
  let A : ℝ := ((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)
  calc
    _ = ∫ ω, Real.exp (-A) *
        Real.exp (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)) ∂P := by
          congr 1
          funext ω
          rw [← Real.exp_add]
          congr 1
          dsimp [A]
          ring
    _ = Real.exp (-A) *
        (∫ ω, Real.exp
          (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)) ∂P) := by
          rw [integral_const_mul]
    _ = 1 := by
          rw [hLap, ← Real.exp_add]
          simp [A]
