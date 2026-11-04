-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_laplace_exponent_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:21:25.172013+00:00
-- url     : https://prove2.me/submissions/abafbc7a-2326-4d40-83d4-5746373d2ee9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- In the source's original Levy-Khintchine convention, zero jump measure
reduces the Laplace exponent to drift plus Gaussian quadratic exponent.
This identifies the Gaussian law scale but asserts no Brownian representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (θ : ℝ) :
    Y.ψ θ = Y.c * θ + Y.σ ^ 2 * θ ^ 2 / 2 := by
  simp [SpectrallyNegativeLevy.ψ, laplaceExponent, hν]
