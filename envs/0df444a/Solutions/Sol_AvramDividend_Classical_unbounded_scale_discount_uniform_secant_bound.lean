-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_uniform_secant_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:22:50.41708+00:00
-- url     : https://prove2.me/submissions/2fa07c43-e4de-4734-8b4e-2b8d48228b07

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_sandwich
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- On a bounded discount range, a single endpoint self-convolution controls changes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ Q : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hQ : 0 ≤ Q) (hq12 : q₁ < q₂) (hq2Q : q₂ ≤ Q)
    (W₁ W₂ WQ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hWQ : IsScaleFunction X Q WQ) :
    ∀ x : ℝ, 0 < x →
      0 ≤ W₂ x - W₁ x ∧
        W₂ x - W₁ x ≤ (q₂ - q₁) *
          ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) := by
  intro x hx
  have hs := unbounded_scale_discount_secant_sandwich
    X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ x hx
  have hfirst := unbounded_scale_discount_convolution_order
    X hnbv q₂ q₂ Q hq₂ hq₂ hQ le_rfl hq2Q
    W₂ W₂ WQ hW₂ hW₂ hWQ x hx
  have hsecond := unbounded_scale_discount_convolution_order
    X hnbv q₂ Q Q hq₂ hQ hQ hq2Q le_rfl
    W₂ WQ WQ hW₂ hWQ hWQ x hx
  have hslope : (W₂ x - W₁ x) / (q₂ - q₁) ≤
      ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) :=
    hs.2.trans (hfirst.trans hsecond)
  have hgappos : 0 < q₂ - q₁ := sub_pos.mpr hq12
  have hstrict := unbounded_scale_discount_strict_monotone
    X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ x hx
  have hcross := (div_le_iff₀ hgappos).mp hslope
  exact ⟨sub_nonneg.mpr hstrict.le, by simpa only [mul_comm] using hcross⟩
