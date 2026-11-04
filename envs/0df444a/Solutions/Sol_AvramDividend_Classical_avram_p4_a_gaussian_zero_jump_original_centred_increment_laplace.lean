-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:03:00.031664+00:00
-- url     : https://prove2.me/submissions/c3593738-9ff5-41e4-a97f-48d0c70bb313

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Each original zero-jump deterministic increment has the Gaussian Laplace transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
       (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)) ∂P) =
      Real.exp (((t - s : ℝ≥0) : ℝ) *
        (Y.σ ^ 2 * θ ^ 2 / 2)) := by
  have hMeas : Measurable (fun z : ℝ =>
      Real.exp (θ * (z - ((t - s : ℝ≥0) : ℝ) * Y.c))) := by
    fun_prop
  have hId := (Y.stationaryIncrements s t hst).comp hMeas
  have hEq := hId.integral_eq
  calc
    _ = ∫ ω, Real.exp
          (θ * (Y.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * Y.c)) ∂P := by
            simpa only [Function.comp_def] using hEq
    _ = Real.exp (((t - s : ℝ≥0) : ℝ) *
          (Y.σ ^ 2 * θ ^ 2 / 2)) :=
          avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
            Y hν (t - s) θ hθ
