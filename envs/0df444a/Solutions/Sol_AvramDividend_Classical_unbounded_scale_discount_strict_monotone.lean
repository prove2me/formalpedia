-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_strict_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:14:37.168502+00:00
-- url     : https://prove2.me/submissions/af25b0f4-cf69-4dc0-895c-952c2baf41d4

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Strictly increasing a nonnegative discount strictly increases the
unbounded-variation scale function at every positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ < q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x → W₁ x < W₂ x := by
  have hres := unbounded_scale_resolvent_convolution
    X hnbv q₁ q₂ hq₁ hq₂ W₁ W₂ hW₁ hW₂
  intro x hx
  have hLeft : ContinuousOn W₁ (Icc (0 : ℝ) x) :=
    hW₁.2.2.1.mono (by intro s hs; exact hs.1)
  have hRight : ContinuousOn (fun s : ℝ => W₂ (x - s))
      (Icc (0 : ℝ) x) :=
    hW₂.2.2.1.comp
      (continuous_const.sub continuous_id).continuousOn
      (by intro s hs; exact sub_nonneg.mpr hs.2)
  have hFcont : ContinuousOn (fun s : ℝ => W₁ s * W₂ (x - s))
      (Icc (0 : ℝ) x) := hLeft.mul hRight
  have hC : 0 < ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s) := by
    rw [← intervalIntegral.integral_of_le hx.le]
    apply intervalIntegral.integral_pos hx hFcont
    · intro s hs
      exact mul_nonneg (hW₁.2.1 s hs.1.le)
        (hW₂.2.1 (x - s) (sub_nonneg.mpr hs.2))
    · refine ⟨x / 2, ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · apply mul_pos
        · exact scaleFunction_strict_pos_of_unbounded_variation
            X q₁ W₁ hW₁ hnbv (x / 2) (by linarith)
        · exact scaleFunction_strict_pos_of_unbounded_variation
            X q₂ W₂ hW₂ hnbv (x - x / 2) (by linarith)
  have hprod : 0 < (q₂ - q₁) *
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) :=
    mul_pos (sub_pos.mpr hq) hC
  linarith [hres x hx]
