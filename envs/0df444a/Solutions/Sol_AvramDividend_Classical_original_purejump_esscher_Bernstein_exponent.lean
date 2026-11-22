-- Prove2me | solution 1 for AvramDividend.Classical.original_purejump_esscher_Bernstein_exponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:47:54.389161+00:00
-- url     : https://prove2.me/submissions/e74645d5-6dde-4533-ba57-5ea1070776ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_original_purejump_laplace_exponent_tail
import Theorems.Thm_AvramDividend_Classical_esscher_tail_integral_shift_identity
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (Φ : ℝ) (hΦ : 0 < Φ)
    (hRoot : X.ψ Φ = 0) (s : ℝ) (hs : 0 ≤ s) :
    X.ψ (Φ + s) / (Φ + s) =
      (∫ t in Ioi (0 : ℝ),
        Real.exp (-(Φ * t)) * (1 - Real.exp (-(s * t))) *
          (X.ν (Iio (-t))).toReal) := by
  let κ : ℝ → ℝ := fun t => (X.ν (Iio (-t))).toReal
  let m : ℝ := X.c + ∫ y in Iic (-1 : ℝ), y ∂X.ν
  have hNext := original_purejump_laplace_exponent_tail
    X hX hσ (Φ + s) (add_pos_of_pos_of_nonneg hΦ hs)
  have hBase := original_purejump_laplace_exponent_tail
    X hX hσ Φ hΦ
  have hNextInt : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-((Φ + s) * t))) * κ t)
      (Ioi (0 : ℝ)) := by
    simpa only [κ, neg_mul] using hNext.1
  have hBaseInt : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-(Φ * t))) * κ t)
      (Ioi (0 : ℝ)) := by
    simpa only [κ, neg_mul] using hBase.1
  have hShift := esscher_tail_integral_shift_identity
    κ Φ s hNextInt hBaseInt
  have hn : X.ψ (Φ + s) / (Φ + s) =
      m + ∫ t in Ioi (0 : ℝ),
        (1 - Real.exp (-((Φ + s) * t))) * κ t := by
    simpa only [m, κ, neg_mul] using hNext.2
  have hb : X.ψ Φ / Φ =
      m + ∫ t in Ioi (0 : ℝ),
        (1 - Real.exp (-(Φ * t))) * κ t := by
    simpa only [m, κ, neg_mul] using hBase.2
  calc
    X.ψ (Φ + s) / (Φ + s) =
      m + (∫ t in Ioi (0 : ℝ),
        (1 - Real.exp (-((Φ + s) * t))) * κ t) := hn
    _ = X.ψ Φ / Φ + (
      (∫ t in Ioi (0 : ℝ),
        (1 - Real.exp (-((Φ + s) * t))) * κ t) -
      (∫ t in Ioi (0 : ℝ),
        (1 - Real.exp (-(Φ * t))) * κ t)) := by
        rw [hb]
        ring
    _ = (∫ t in Ioi (0 : ℝ),
      Real.exp (-(Φ * t)) * (1 - Real.exp (-(s * t))) * κ t) := by
        rw [hRoot, zero_div, zero_add, hShift]