-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_zero_secant_strict_increasing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:18:49.472825+00:00
-- url     : https://prove2.me/submissions/880495e3-bdf4-4f95-88e9-c3d7fcaa3cca

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_chord
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive zero-based scale-function discount secants strictly increase with q. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (W₀ Wa Wb : ℝ → ℝ)
    (hW₀ : IsScaleFunction X 0 W₀)
    (hWa : IsScaleFunction X a Wa)
    (hWb : IsScaleFunction X b Wb) :
    ∀ x : ℝ, 0 < x →
      (Wa x - W₀ x) / a < (Wb x - W₀ x) / b := by
  intro x hx
  have ha0 : 0 ≤ a := le_of_lt ha
  have hb0 : 0 ≤ b := le_trans ha0 (le_of_lt hab)
  have hb : 0 < b := lt_trans ha hab
  have hchord := unbounded_scale_discount_strict_chord
    X hnbv 0 a b le_rfl ha0 hb0 ha hab
    W₀ Wa Wb hW₀ hWa hWb x hx
  apply (div_lt_div_iff₀ ha hb).2
  nlinarith [hchord]
