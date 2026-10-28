-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_zero_secant_family_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:29:04.62939+00:00
-- url     : https://prove2.me/submissions/fdc05411-2e6a-462b-8c54-33c21f778534

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_zero_secant_strict_increasing
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Zero-based scale discount secants form a strictly increasing function of positive q. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      StrictMonoOn (fun q : ℝ => (W q x - W 0 x) / q) (Ioi (0 : ℝ)) := by
  intro x hx a ha b hb hab
  have hapos : 0 < a := ha
  have hbpos : 0 < b := hb
  exact unbounded_scale_discount_zero_secant_strict_increasing
    X hnbv a b hapos hab (W 0) (W a) (W b)
    (hW 0 le_rfl) (hW a hapos.le) (hW b hbpos.le) x hx
