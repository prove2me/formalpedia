-- Prove2me | solution 1 for AvramDividend.Classical.positive_nonnegative_interval_integral_le_global
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:29:14.554856+00:00
-- url     : https://prove2.me/submissions/4edbb9c7-e639-4fb8-9138-bf669bb9e1b1

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in Ioc (0 : ℝ) x, f t ∂volume) ≤
      (∫ t in Ioi (0 : ℝ), f t ∂volume) := by
  have hsubset : Ioc (0 : ℝ) x ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact ht.1
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ f t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpos t ht
  exact setIntegral_mono_set hf hnonneg (Filter.Eventually.of_forall hsubset)
