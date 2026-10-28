-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_discounted_scale_zero_mean_forces_nonpositive_increment_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:13:38.613314+00:00
-- url     : https://prove2.me/submissions/f38bfbfc-47a4-44b5-b15f-44f24ec0aab9

import Theorems.Thm_AvramDividend_Classical_discounted_scale_zero_mean_forces_zero_ae
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (hW0 : W 0 = 0) (t : ℝ≥0)
    (hInt : Integrable
      (fun ω : Ω => Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) P)
    (hMean : (∫ ω : Ω, Real.exp (-(q * (t : ℝ))) *
      W (X.X t ω) ∂P) = W 0) :
    ∀ᵐ ω ∂P, X.X t ω ≤ 0 := by
  filter_upwards [AvramDividend.Classical.discounted_scale_zero_mean_forces_zero_ae X q W hW hW0 t hInt hMean]
    with ω hω
  by_contra h
  push_neg at h
  have := AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv _ h
  linarith
