-- Prove2me | solution 1 for AvramDividend.Classical.restrict_Ico_eq_of_local_Ico_mass_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:53:23.438932+00:00
-- url     : https://prove2.me/submissions/23112b51-6aa5-47df-80aa-fe60ca38996f

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ] (r : ℝ)
    (h : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ r →
      μ (Ico a b) = ν (Ico a b)) :
    μ.restrict (Ico 0 r) = ν.restrict (Ico 0 r) := by
  classical
  have hinter (a b : ℝ) :
      Ico a b ∩ Ico 0 r = Ico (max a 0) (min b r) := by
    ext x
    simp only [mem_inter_iff, mem_Ico, max_le_iff, lt_min_iff]
    tauto
  have hclip (a b : ℝ) :
      μ (Ico (max a 0) (min b r)) =
        ν (Ico (max a 0) (min b r)) := by
    by_cases hc : max a 0 ≤ min b r
    · exact h (max a 0) (min b r) (le_max_right a 0)
        hc (min_le_right b r)
    · have hempty : Ico (max a 0) (min b r) = (∅ : Set ℝ) := by
        ext x
        constructor
        · intro hx
          exact (hc (le_of_lt (lt_of_le_of_lt hx.1 hx.2))).elim
        · intro hx
          simp at hx
      simp only [hempty, measure_empty]
  apply Measure.ext_of_Ico
  intro a b hab
  rw [Measure.restrict_apply measurableSet_Ico,
      Measure.restrict_apply measurableSet_Ico, hinter]
  exact hclip a b
