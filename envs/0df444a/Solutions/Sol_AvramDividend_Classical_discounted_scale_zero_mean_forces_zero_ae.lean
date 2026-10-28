-- Prove2me | solution 1 for AvramDividend.Classical.discounted_scale_zero_mean_forces_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:08:51.982765+00:00
-- url     : https://prove2.me/submissions/72b387da-5274-4dd4-b0cf-ea70cd73ef85

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hW0 : W 0 = 0) (t : ℝ≥0)
    (hInt : Integrable
      (fun ω : Ω => Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) P)
    (hMean : (∫ ω : Ω, Real.exp (-(q * (t : ℝ))) *
      W (X.X t ω) ∂P) = W 0) :
    ∀ᵐ ω ∂P, W (X.X t ω) = 0 := by
  have hWnn : ∀ y, 0 ≤ W y := by
    intro y
    rcases lt_or_ge y 0 with h | h
    · rw [hW.1 y h]
    · exact hW.2.1 y h
  have hnn : 0 ≤ᵐ[P] fun ω => Real.exp (-(q * (t : ℝ))) * W (X.X t ω) :=
    Filter.Eventually.of_forall fun ω => mul_nonneg (Real.exp_pos _).le (hWnn _)
  rw [hW0] at hMean
  have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hInt).1 hMean
  filter_upwards [h0] with ω hω
  simpa [(Real.exp_pos _).ne'] using hω
