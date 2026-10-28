-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_zero_secant_positive_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:27:14.076387+00:00
-- url     : https://prove2.me/submissions/692b5615-89f3-4a27-bed3-8335023f01b8

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_uniform_secant_bound
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The positive-discount secant from zero is strictly positive and bounded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q Q : ℝ) (hq : 0 < q) (hqQ : q ≤ Q)
    (W₀ Wq WQ : ℝ → ℝ)
    (hW₀ : IsScaleFunction X 0 W₀)
    (hWq : IsScaleFunction X q Wq)
    (hWQ : IsScaleFunction X Q WQ) :
    ∀ x : ℝ, 0 < x →
      0 < (Wq x - W₀ x) / q ∧
      (Wq x - W₀ x) / q ≤
        ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) := by
  intro x hx
  have hq0 : 0 ≤ q := le_of_lt hq
  have hQ : 0 ≤ Q := le_trans hq0 hqQ
  have hs := unbounded_scale_discount_uniform_secant_bound
    X hnbv 0 q Q le_rfl hq0 hQ hq hqQ
    W₀ Wq WQ hW₀ hWq hWQ x hx
  have hstrict := unbounded_scale_discount_strict_monotone
    X hnbv 0 q le_rfl hq0 hq W₀ Wq hW₀ hWq x hx
  simpa only [sub_zero] using
    (show 0 < (Wq x - W₀ x) / (q - 0) ∧
      (Wq x - W₀ x) / (q - 0) ≤
        ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) from
      ⟨div_pos (sub_pos.mpr hstrict) (sub_pos.mpr hq),
       (div_le_iff₀ (sub_pos.mpr hq)).2
         (by simpa only [mul_comm] using hs.2)⟩)
