-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_strict_convex_secants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:57:20.573525+00:00
-- url     : https://prove2.me/submissions/14153c3b-6167-49b3-9fc3-ede694308c8f

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Strict discount secant convexity at each positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ q₃ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq₃ : 0 ≤ q₃) (hq12 : q₁ < q₂) (hq23 : q₂ < q₃)
    (W₁ W₂ W₃ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hW₃ : IsScaleFunction X q₃ W₃) :
    ∀ x : ℝ, 0 < x →
      (W₂ x - W₁ x) / (q₂ - q₁) <
        (W₃ x - W₂ x) / (q₃ - q₂) := by
  intro x hx
  have hL1 : ContinuousOn W₁ (Icc (0 : ℝ) x) :=
    hW₁.2.2.1.mono (by intro s hs; exact hs.1)
  have hL2 : ContinuousOn W₂ (Icc (0 : ℝ) x) :=
    hW₂.2.2.1.mono (by intro s hs; exact hs.1)
  have hR2 : ContinuousOn (fun s : ℝ => W₂ (x - s))
      (Icc (0 : ℝ) x) :=
    hW₂.2.2.1.comp (continuous_const.sub continuous_id).continuousOn
      (by intro s hs; exact sub_nonneg.mpr hs.2)
  have hR3 : ContinuousOn (fun s : ℝ => W₃ (x - s))
      (Icc (0 : ℝ) x) :=
    hW₃.2.2.1.comp (continuous_const.sub continuous_id).continuousOn
      (by intro s hs; exact sub_nonneg.mpr hs.2)
  have hC : (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) <
      (∫ s in Ioc (0 : ℝ) x, W₂ s * W₃ (x - s)) := by
    rw [← intervalIntegral.integral_of_le hx.le,
      ← intervalIntegral.integral_of_le hx.le]
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hx (hL1.mul hR2) (hL2.mul hR3)
    · intro s hs
      have hs0 : 0 < s := hs.1
      have hxs : 0 ≤ x - s := sub_nonneg.mpr hs.2
      have h12 := unbounded_scale_discount_strict_monotone
        X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ s hs0
      by_cases hright : x - s = 0
      · have hz2 := unbounded_scale_zero_origin_nonnegative_discount
          X hnbv q₂ hq₂ W₂ hW₂
        have hz3 := unbounded_scale_zero_origin_nonnegative_discount
          X hnbv q₃ hq₃ W₃ hW₃
        simp [hright, hz2, hz3]
      · have hxspos : 0 < x - s := lt_of_le_of_ne hxs (Ne.symm hright)
        have h23 := unbounded_scale_discount_strict_monotone
          X hnbv q₂ q₃ hq₂ hq₃ hq23 W₂ W₃ hW₂ hW₃ (x - s) hxspos
        exact (mul_le_mul_of_nonneg_right (le_of_lt h12)
          (hW₂.2.1 (x - s) hxs)).trans
          (mul_le_mul_of_nonneg_left (le_of_lt h23) (hW₂.2.1 s hs0.le))
    · refine ⟨x / 2, ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · have h12 := unbounded_scale_discount_strict_monotone
          X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ (x / 2) (by linarith)
        have h23 := unbounded_scale_discount_strict_monotone
          X hnbv q₂ q₃ hq₂ hq₃ hq23 W₂ W₃ hW₂ hW₃
          (x - x / 2) (by linarith)
        have hp2 := scaleFunction_strict_pos_of_unbounded_variation
          X q₂ W₂ hW₂ hnbv (x / 2) (by linarith)
        have hpR := scaleFunction_strict_pos_of_unbounded_variation
          X q₂ W₂ hW₂ hnbv (x - x / 2) (by linarith)
        exact (mul_lt_mul_of_pos_right h12 hpR).trans
          (mul_lt_mul_of_pos_left h23 hp2)
  have hsec12 := unbounded_scale_discount_secant_convolution
    X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ x hx
  have hsec23 := unbounded_scale_discount_secant_convolution
    X hnbv q₂ q₃ hq₂ hq₃ hq23 W₂ W₃ hW₂ hW₃ x hx
  rw [hsec12, hsec23]
  exact hC
