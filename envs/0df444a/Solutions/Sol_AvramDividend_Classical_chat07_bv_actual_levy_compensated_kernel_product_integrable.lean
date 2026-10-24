-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_actual_levy_compensated_kernel_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:03:45.519822+00:00
-- url     : https://prove2.me/submissions/4f8e41c3-68b0-4918-b35c-d5f3cdea52ee

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_bv_positive_jump_kernel_product_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_ae_positive
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Specialise the positive-magnitude kernel bound to the BV Levy jump image. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(θ*p.1)) *
        |W (p.1-p.2) - W p.1 +
          (if p.2 < 1 then p.2*deriv W p.1 else 0)|)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        ((X.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y))) := by
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  let νmag : Measure ℝ :=
    (X.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y)
  haveI : SFinite νmag := by
    dsimp [νmag]
    change SFinite ((X.ν.restrict (Iio (0 : ℝ))).neg)
    infer_instance
  have hpos : ∀ᵐ r ∂νmag, (0 : ℝ) < r :=
    chat07_bv_neg_map_magnitude_ae_positive X
  have hmoment : Integrable (fun r : ℝ => min (1 : ℝ) r) νmag :=
    chat07_bv_neg_map_magnitude_first_moment_integrable X hBV
  exact chat07_bv_positive_jump_kernel_product_integrable
    X q W hW hWmon θ hθ hqθ νmag hpos hmoment
