-- Prove2me | solution 1 for AvramDividend.Classical.restricted_measure_eq_of_Ico_prefix_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T12:53:48.303992+00:00
-- url     : https://prove2.me/submissions/f0dd58fd-c524-41d5-a922-343aef280321

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
open MeasureTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (μ ν : Measure ℝ) (T : ℝ)
    (hfin : μ (Ico 0 T) < ⊤)
    (heq : ∀ a b : ℝ, 0 ≤ a → b ≤ T →
       μ (Ico a b) = ν (Ico a b)) :
    μ.restrict (Ico 0 T) = ν.restrict (Ico 0 T) := by
  have hf : ∀ ⦃a b : ℝ⦄, a < b →
      (μ.restrict (Ico 0 T)) (Ico a b) ≠ ⊤ := by
    intro a b hab
    rw [Measure.restrict_apply measurableSet_Ico]
    have hle : μ (Ico a b ∩ Ico 0 T) ≤ μ (Ico 0 T) :=
      measure_mono inter_subset_right
    exact ne_of_lt (lt_of_le_of_lt hle hfin)
  apply Measure.ext_of_Ico' _ _ hf
  intro a b hab
  rw [Measure.restrict_apply measurableSet_Ico,
      Measure.restrict_apply measurableSet_Ico, Ico_inter_Ico]
  exact heq (max a 0) (min b T) (le_max_right _ _) (min_le_right _ _)
