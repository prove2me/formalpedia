-- Prove2me | solution 1 for AvramDividend.Classical.excursion_height_level_null_of_markov_bad_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:01:12.447603+00:00
-- url     : https://prove2.me/submissions/ff2957ef-df27-4ec6-a2f5-af879cbd904d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Theorems.Thm_AvramDividend_Classical_reflected_excursion_height_level_null_of_ae_negative_on_hitting

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {E : Type*} [mE : MeasurableSpace E]
    (n : Measure E) (P : Measure (ℝ≥0 → ℝ))
    (S Y : E → ℝ≥0 → ℝ) (T ζ H : E → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ e : E, H e = x →
      T e < ζ e ∧ Monotone (S e) ∧
      S e (T e) - Y e (T e) = (x : ℝ) ∧
      ∀ t : ℝ≥0, T e ≤ t → t < ζ e →
        S e t - Y e t ≤ (x : ℝ))
    (hRegP : ∀ᵐ f ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ f s < 0)
    (hExcursionMarkovBad :
      n {e : E | T e < ζ e ∧
        ¬ ∀ ε : ℝ≥0, 0 < ε →
          ∃ s : ℝ≥0, s < ε ∧
            Y e (T e + s) - Y e (T e) < 0} =
      n {e : E | T e < ζ e} *
        P {f : ℝ≥0 → ℝ | ¬ ∀ ε : ℝ≥0, 0 < ε →
          ∃ s : ℝ≥0, s < ε ∧ f s < 0}) :
    n {e : E | H e = x} = 0 := by
  have hBadP :
      P {f : ℝ≥0 → ℝ | ¬ ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ f s < 0} = 0 :=
    ae_iff.mp hRegP
  have hBadN :
      n {e : E | T e < ζ e ∧
        ¬ ∀ ε : ℝ≥0, 0 < ε →
          ∃ s : ℝ≥0, s < ε ∧
            Y e (T e + s) - Y e (T e) < 0} = 0 := by
    rw [hExcursionMarkovBad, hBadP, mul_zero]
  have hNegOnHit : ∀ᵐ e ∂n, T e < ζ e →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          Y e (T e + s) < Y e (T e) := by
    apply (ae_iff).2
    have hBadN' :
        n {e : E | ¬ (T e < ζ e →
          ∀ ε : ℝ≥0, 0 < ε →
            ∃ s : ℝ≥0, s < ε ∧
              Y e (T e + s) - Y e (T e) < 0)} = 0 := by
      simpa only [_root_.not_imp] using hBadN
    simpa only [sub_lt_zero] using hBadN'
  exact reflected_excursion_height_level_null_of_ae_negative_on_hitting
    n S Y T ζ H x hAtLevel hNegOnHit
