-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_unstopped_scale_martingale_forces_nonpositive_paths
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:19:47.80466+00:00
-- url     : https://prove2.me/submissions/4b49da7f-75c0-4b8f-bd97-28610dac821d

import Theorems.Thm_AvramDividend_Classical_nonnegative_zero_initial_martingale_vanishes_ae
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Probability.Martingale.Basic

open AvramDividend.Classical MeasureTheory
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (hW0 : W 0 = 0)
    (hStart : ∀ᵐ ω ∂P, X.X 0 ω = 0)
    (hMart : Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X.X t ω ≤ 0 := by
  have hWnn : ∀ y, 0 ≤ W y := by
    intro y
    rcases lt_or_ge y 0 with h | h
    · rw [hW.1 y h]
    · exact hW.2.1 y h
  have hv := AvramDividend.Classical.nonnegative_zero_initial_martingale_vanishes_ae _ hMart
    (fun t => Filter.Eventually.of_forall fun ω => mul_nonneg (Real.exp_pos _).le (hWnn _))
    (by
      filter_upwards [hStart] with ω hω
      simp [hω, hW0])
  intro t
  filter_upwards [hv t] with ω hω
  by_contra h
  push_neg at h
  have h1 := AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv _ h
  have h2 : Real.exp (-(q * (t : ℝ))) * W (X.X t ω) = 0 := hω
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact (Real.exp_pos _).ne' h3
  · linarith
