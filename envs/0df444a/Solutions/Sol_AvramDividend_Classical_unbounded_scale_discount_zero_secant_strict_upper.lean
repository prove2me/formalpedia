-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_zero_secant_strict_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:29:26.938183+00:00
-- url     : https://prove2.me/submissions/f0bfcfd9-7e3c-404f-9f28-0eaae574f281

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_convex_secants
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Zero-based discount secants admit a strict endpoint-convolution upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q Q : ℝ) (hq : 0 < q) (hqQ : q < Q)
    (W₀ Wq WQ : ℝ → ℝ)
    (hW₀ : IsScaleFunction X 0 W₀)
    (hWq : IsScaleFunction X q Wq)
    (hWQ : IsScaleFunction X Q WQ) :
    ∀ x : ℝ, 0 < x →
      (Wq x - W₀ x) / q <
        ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) := by
  intro x hx
  have hq0 : 0 ≤ q := le_of_lt hq
  have hQ : 0 ≤ Q := le_trans hq0 (le_of_lt hqQ)
  have hs := unbounded_scale_discount_strict_convex_secants
    X hnbv 0 q Q le_rfl hq0 hQ hq hqQ
    W₀ Wq WQ hW₀ hWq hWQ x hx
  have hsec := unbounded_scale_discount_secant_convolution
    X hnbv q Q hq0 hQ hqQ Wq WQ hWq hWQ x hx
  have horder := unbounded_scale_discount_convolution_order
    X hnbv q Q Q hq0 hQ hQ hqQ.le le_rfl
    Wq WQ WQ hWq hWQ hWQ x hx
  rw [hsec] at hs
  simpa only [sub_zero] using lt_of_lt_of_le hs horder
