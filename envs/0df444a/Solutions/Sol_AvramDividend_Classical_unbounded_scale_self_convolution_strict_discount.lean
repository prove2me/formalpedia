-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_self_convolution_strict_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:17:35.914651+00:00
-- url     : https://prove2.me/submissions/737cd958-a685-4fde-a92b-07d46442e1d4

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Self-convolution grows strictly as the nonnegative discount increases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq12 : q₁ < q₂) (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₁ (x - s)) <
        ∫ s in Ioc (0 : ℝ) x, W₂ s * W₂ (x - s) := by
  intro x hx
  have hL1 : ContinuousOn W₁ (Icc (0 : ℝ) x) :=
    hW₁.2.2.1.mono (by intro s hs; exact hs.1)
  have hL2 : ContinuousOn W₂ (Icc (0 : ℝ) x) :=
    hW₂.2.2.1.mono (by intro s hs; exact hs.1)
  have hR1 : ContinuousOn (fun s : ℝ => W₁ (x - s))
      (Icc (0 : ℝ) x) :=
    hW₁.2.2.1.comp (continuous_const.sub continuous_id).continuousOn
      (by intro s hs; exact sub_nonneg.mpr hs.2)
  have hR2 : ContinuousOn (fun s : ℝ => W₂ (x - s))
      (Icc (0 : ℝ) x) :=
    hW₂.2.2.1.comp (continuous_const.sub continuous_id).continuousOn
      (by intro s hs; exact sub_nonneg.mpr hs.2)
  rw [← intervalIntegral.integral_of_le hx.le,
    ← intervalIntegral.integral_of_le hx.le]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hx (hL1.mul hR1) (hL2.mul hR2)
  · intro s hs
    have hs0 : 0 < s := hs.1
    have hxs : 0 ≤ x - s := sub_nonneg.mpr hs.2
    have h12 := unbounded_scale_discount_strict_monotone
      X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ s hs0
    by_cases hright : x - s = 0
    · have hz1 := unbounded_scale_zero_origin_nonnegative_discount
        X hnbv q₁ hq₁ W₁ hW₁
      have hz2 := unbounded_scale_zero_origin_nonnegative_discount
        X hnbv q₂ hq₂ W₂ hW₂
      simp [hright, hz1, hz2]
    · have hxspos : 0 < x - s := lt_of_le_of_ne hxs (Ne.symm hright)
      have h12r := unbounded_scale_discount_strict_monotone
        X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ (x - s) hxspos
      exact (mul_le_mul_of_nonneg_right (le_of_lt h12)
        (hW₁.2.1 (x - s) hxs)).trans
        (mul_le_mul_of_nonneg_left (le_of_lt h12r) (hW₂.2.1 s hs0.le))
  · refine ⟨x / 2, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · have h12 := unbounded_scale_discount_strict_monotone
        X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ (x / 2) (by linarith)
      have h12r := unbounded_scale_discount_strict_monotone
        X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂
        (x - x / 2) (by linarith)
      have hp1 := scaleFunction_strict_pos_of_unbounded_variation
        X q₁ W₁ hW₁ hnbv (x - x / 2) (by linarith)
      have hp2 := scaleFunction_strict_pos_of_unbounded_variation
        X q₂ W₂ hW₂ hnbv (x / 2) (by linarith)
      exact (mul_lt_mul_of_pos_right h12 hp1).trans
        (mul_lt_mul_of_pos_left h12r hp2)
