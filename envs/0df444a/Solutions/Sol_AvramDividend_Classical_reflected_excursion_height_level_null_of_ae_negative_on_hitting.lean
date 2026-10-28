-- Prove2me | solution 1 for AvramDividend.Classical.reflected_excursion_height_level_null_of_ae_negative_on_hitting
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:20:30.843344+00:00
-- url     : https://prove2.me/submissions/71f0178b-8feb-43f6-8578-090095a47d61

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_reflected_excursion_exceeds_hit_height_of_local_negative_increments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {E : Type*} [mE : MeasurableSpace E] (n : Measure E)
    (S Y : E → ℝ≥0 → ℝ)
    (T ζ H : E → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ e : E, H e = x →
      T e < ζ e ∧
      Monotone (S e) ∧
      S e (T e) - Y e (T e) = (x : ℝ) ∧
      ∀ t : ℝ≥0, T e ≤ t → t < ζ e →
        S e t - Y e t ≤ (x : ℝ))
    (hNegOnHitAE : ∀ᵐ e ∂n, T e < ζ e →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          Y e (T e + s) < Y e (T e)) :
    n {e : E | H e = x} = 0 := by
  have hNoLevel : ∀ᵐ e ∂n, H e ≠ x := by
    filter_upwards [hNegOnHitAE] with e hneg hEq
    obtain ⟨hT, hS, hHit, hMax⟩ := hAtLevel e hEq
    obtain ⟨t, htLeft, htRight, htAbove⟩ :=
      reflected_excursion_exceeds_hit_height_of_local_negative_increments
        (S e) (Y e) (T e) (ζ e) x hT hS hHit (hneg hT)
    exact (not_lt_of_ge (hMax t htLeft htRight)) htAbove
  simpa only [not_ne_iff] using (ae_iff.mp hNoLevel)
