-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_preserves_order_and_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:49:14.471986+00:00
-- url     : https://prove2.me/submissions/ddf62c10-f93d-4016-9306-035f5c916072

import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (f : ℝ → ℝ) (hf : Monotone f)
    (a b : ℝ) (hbound : ∀ z, a ≤ f z ∧ f z ≤ b)
    (hInt : ∀ x : ℝ, Integrable (fun ω => f (x + X.X t ω)) P) :
    Monotone (fun x : ℝ => ∫ ω, f (x + X.X t ω) ∂P) ∧
    (∀ x : ℝ, a ≤ (∫ ω, f (x + X.X t ω) ∂P) ∧
      (∫ ω, f (x + X.X t ω) ∂P) ≤ b) := by
  letI : IsProbabilityMeasure P := X.isProbability
  constructor
  · intro x y hxy
    apply MeasureTheory.integral_mono_ae (hInt x) (hInt y)
    filter_upwards [] with ω
    exact hf (add_le_add_left hxy (X.X t ω))
  · intro x
    constructor
    · have hmono : (∫ _ : Ω, a ∂P) ≤
          (∫ ω, f (x + X.X t ω) ∂P) :=
        MeasureTheory.integral_mono_ae
          (integrable_const a) (hInt x) (by
            filter_upwards [] with ω
            exact (hbound (x + X.X t ω)).1)
      simpa using hmono
    · have hmono : (∫ ω, f (x + X.X t ω) ∂P) ≤
          (∫ _ : Ω, b ∂P) :=
        MeasureTheory.integral_mono_ae
          (hInt x) (integrable_const b) (by
            filter_upwards [] with ω
            exact (hbound (x + X.X t ω)).2)
      simpa using hmono
