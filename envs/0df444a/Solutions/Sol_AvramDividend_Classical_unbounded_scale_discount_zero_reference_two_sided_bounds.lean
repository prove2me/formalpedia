-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_zero_reference_two_sided_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:11:56.674734+00:00
-- url     : https://prove2.me/submissions/cacd5b79-60b1-4016-acef-205a182d1e88

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_two_sided_linear_bounds
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive-discount deviation from the undiscounted scale has explicit integral bounds. -/
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
      q * (∫ s in Ioc (0 : ℝ) x, W₀ s * W₀ (x - s)) ≤
        Wq x - W₀ x ∧
      Wq x - W₀ x ≤ q *
        (∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s)) := by
  intro x hx
  have hq0 : 0 ≤ q := le_of_lt hq
  have hQ : 0 ≤ Q := le_trans hq0 hqQ
  have hbound := unbounded_scale_discount_two_sided_linear_bounds
    X hnbv 0 q Q le_rfl hq0 hQ hq hqQ
    W₀ W₀ Wq WQ hW₀ hW₀ hWq hWQ x hx
  simpa only [sub_zero] using hbound
