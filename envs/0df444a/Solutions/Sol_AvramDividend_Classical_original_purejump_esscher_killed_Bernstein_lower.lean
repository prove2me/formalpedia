-- Prove2me | solution 1 for AvramDividend.Classical.original_purejump_esscher_killed_Bernstein_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:24:41.819347+00:00
-- url     : https://prove2.me/submissions/3853da6a-b594-41c6-9c1a-17ed24b056f1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_original_purejump_esscher_killed_Bernstein
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_kernel_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (φ : ℝ) (hφ : 0 < φ)
    (hψ : 0 < X.ψ φ) (s : ℝ) (hs : 0 ≤ s) :
    X.ψ φ / φ ≤ X.ψ (φ + s) / (φ + s) ∧
    0 < X.ψ (φ + s) / (φ + s) := by
  have hBern := original_purejump_esscher_killed_Bernstein
    X hX hσ φ hφ s hs
  have hweight : ∀ t ∈ Ioi (0 : ℝ),
      0 ≤ Real.exp (-(φ * t)) *
        (1 - Real.exp (-(s * t))) *
          (X.ν (Iio (-t))).toReal := by
    intro t ht
    have htpos : 0 ≤ t := le_of_lt (by simpa only [mem_Ioi] using ht)
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _)
      (by simpa only [neg_mul] using
        (levy_compensated_exponential_kernel_bounds s t hs htpos).1))
      ENNReal.toReal_nonneg
  have hInt : 0 ≤ (∫ t in Ioi (0 : ℝ),
      Real.exp (-(φ * t)) *
        (1 - Real.exp (-(s * t))) *
          (X.ν (Iio (-t))).toReal) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hweight t ht
  have hpos : 0 < X.ψ φ / φ := div_pos hψ hφ
  constructor
  · rw [hBern]
    linarith
  · rw [hBern]
    linarith
