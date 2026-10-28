-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_convolution_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:46:43.676985+00:00
-- url     : https://prove2.me/submissions/456afaf2-efa1-468f-a921-e8d88dbc7e8e

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Nondecreasing discounts induce ordered causal convolutions,
providing the analytic order property behind convexity in discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ q₃ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq₃ : 0 ≤ q₃) (hq12 : q₁ ≤ q₂) (hq23 : q₂ ≤ q₃)
    (W₁ W₂ W₃ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hW₃ : IsScaleFunction X q₃ W₃) :
    ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) ≤
        ∫ s in Ioc (0 : ℝ) x, W₂ s * W₃ (x - s) := by
  intro x hx
  have hL1 : ContinuousOn W₁ (Icc (0 : ℝ) x) :=
    hW₁.2.2.1.mono (by intro s hs; exact hs.1)
  have hL2 : ContinuousOn W₂ (Icc (0 : ℝ) x) :=
    hW₂.2.2.1.mono (by intro s hs; exact hs.1)
  have hR2 : ContinuousOn (fun s : ℝ => W₂ (x - s))
      (Icc (0 : ℝ) x) :=
    hW₂.2.2.1.comp
      (continuous_const.sub continuous_id).continuousOn
      (by intro s hs; exact sub_nonneg.mpr hs.2)
  have hR3 : ContinuousOn (fun s : ℝ => W₃ (x - s))
      (Icc (0 : ℝ) x) :=
    hW₃.2.2.1.comp
      (continuous_const.sub continuous_id).continuousOn
      (by intro s hs; exact sub_nonneg.mpr hs.2)
  have hA : IntervalIntegrable
      (fun s : ℝ => W₁ s * W₂ (x - s)) volume 0 x :=
    (hL1.mul hR2).intervalIntegrable_of_Icc hx.le
  have hB : IntervalIntegrable
      (fun s : ℝ => W₂ s * W₃ (x - s)) volume 0 x :=
    (hL2.mul hR3).intervalIntegrable_of_Icc hx.le
  have horder := intervalIntegral.integral_mono_on_of_le_Ioo hx.le hA hB
    (by
      intro s hs
      have hs0 : 0 < s := hs.1
      have hxs : 0 < x - s := sub_pos.mpr hs.2
      have h12 := unbounded_scale_discount_monotone
        X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ s hs0
      have h23 := unbounded_scale_discount_monotone
        X hnbv q₂ q₃ hq₂ hq₃ hq23 W₂ W₃ hW₂ hW₃ (x - s) hxs
      calc
        W₁ s * W₂ (x - s) ≤ W₂ s * W₂ (x - s) :=
          mul_le_mul_of_nonneg_right h12 (hW₂.2.1 (x - s) hxs.le)
        _ ≤ W₂ s * W₃ (x - s) :=
          mul_le_mul_of_nonneg_left h23 (hW₂.2.1 s hs0.le))
  simpa only [intervalIntegral.integral_of_le hx.le] using horder
