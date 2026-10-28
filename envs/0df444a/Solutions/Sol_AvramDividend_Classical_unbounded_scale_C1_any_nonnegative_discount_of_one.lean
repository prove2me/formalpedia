-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_C1_any_nonnegative_discount_of_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:42:35.223723+00:00
-- url     : https://prove2.me/submissions/7dc8876d-3797-41b1-8980-a75fe971978f

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_causal_convolution_contDiffOn_one_of_monotone_C1_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hC₁ : ContDiffOn ℝ 1 W₁ (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1 W₂ (Ioi (0 : ℝ)) := by
  have hW₁0 : W₁ 0 = 0 :=
    unbounded_scale_zero_origin_nonnegative_discount X hnbv q₁ hq₁ W₁ hW₁
  have hI : ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, W₂ s * W₁ (x - s) ∂volume)
      (Ioi (0 : ℝ)) :=
    causal_convolution_contDiffOn_one_of_monotone_C1_kernel
      W₂ W₁ hW₂.2.2.1 hW₁.2.2.1 hW₁0 hW₁.2.2.2.1 hC₁
  have hc : ContDiffOn ℝ 1 (fun _ : ℝ => q₁ - q₂) (Ioi (0 : ℝ)) :=
    contDiffOn_const
  have hR : ContDiffOn ℝ 1
      (fun x : ℝ => W₁ x -
        (q₁ - q₂) * ∫ s in Ioc (0 : ℝ) x, W₂ s * W₁ (x - s) ∂volume)
      (Ioi (0 : ℝ)) :=
    hC₁.sub (hc.mul hI)
  apply hR.congr
  intro x hx
  have hres :=
    unbounded_scale_resolvent_convolution
      X hnbv q₂ q₁ hq₂ hq₁ W₂ W₁ hW₂ hW₁ x hx
  linarith
