-- Prove2me | solution 1 for AvramDividend.Classical.measure_restrict_Ioc_eq_of_local_Ioc_agreement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:47:15.383677+00:00
-- url     : https://prove2.me/submissions/275e4a47-35c1-4fe3-9f7d-11e1d83f92e2

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ ν : Measure ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hFinite : μ (Ioc 0 T) < ⊤)
    (hEq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      μ (Ioc s t) = ν (Ioc s t)) :
    μ.restrict (Ioc 0 T) = ν.restrict (Ioc 0 T) := by
  letI : IsFiniteMeasure (μ.restrict (Ioc (0 : ℝ) T)) := by
    refine ⟨?_⟩
    simpa using hFinite
  apply Measure.ext_of_Ioc_finite
      (μ.restrict (Ioc (0 : ℝ) T))
      (ν.restrict (Ioc (0 : ℝ) T))
  · simpa using hEq 0 T le_rfl hT le_rfl
  · intro a b hab
    have hinter :
        Ioc a b ∩ Ioc (0 : ℝ) T =
          Ioc (max a 0) (min b T) := by
      ext x
      simp [lt_min_iff, max_lt_iff, and_comm, and_left_comm, and_assoc]
    have hlocal :
        μ (Ioc (max a 0) (min b T)) =
          ν (Ioc (max a 0) (min b T)) := by
      by_cases hbound : max a 0 ≤ min b T
      · exact hEq (max a 0) (min b T)
          (le_max_right _ _) hbound (min_le_right _ _)
      · have hEmpty :
            Ioc (max a 0) (min b T) = ∅ :=
          Set.Ioc_eq_empty (fun hlt => hbound (le_of_lt hlt))
        simp [hEmpty]
    simpa [Measure.restrict_apply, hinter] using hlocal
