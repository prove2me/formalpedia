-- Prove2me | solution 1 for AvramDividend.Classical.strictLowerCrossingClock_ne_contact_of_positiveRightGerm_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T10:32:32.588376+00:00
-- url     : https://prove2.me/submissions/77587f8c-0bb7-4523-bcd1-394db2e96626

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-- A strict lower-crossing infimum cannot meet its boundary when the
    path has a nonnegative right-hand germ beyond the infimum. -/
theorem solution
    (f : ℝ≥0 → ℝ) (b : ℝ) (τ : ℝ≥0)
    (hτ : (τ : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : f t < b), (t : ℝ≥0∞)))
    (hRight : ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, τ < t → t < τ + ε → b ≤ f t) :
    f τ ≠ b := by
  intro hContact
  obtain ⟨ε, hε, hGerm⟩ := hRight
  have hτLt : (τ : ℝ≥0∞) < ((τ + ε : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr (lt_add_of_pos_right τ hε)
  have hClockBound :
      ((τ + ε : ℝ≥0) : ℝ≥0∞) ≤
        (⨅ (t : ℝ≥0) (_ : f t < b), (t : ℝ≥0∞)) := by
    refine le_iInf fun t => le_iInf fun htCross => ?_
    have htGe : τ ≤ t := by
      apply ENNReal.coe_le_coe.mp
      calc
        (τ : ℝ≥0∞) =
            (⨅ (u : ℝ≥0) (_ : f u < b), (u : ℝ≥0∞)) := hτ
        _ ≤ (⨅ (_ : f t < b), (t : ℝ≥0∞)) :=
          iInf_le (fun u : ℝ≥0 => ⨅ (_ : f u < b), (u : ℝ≥0∞)) t
        _ ≤ (t : ℝ≥0∞) :=
          iInf_le (fun (_ : f t < b) => (t : ℝ≥0∞)) htCross
    rcases lt_or_eq_of_le htGe with htGt | htEq
    · have htFar : τ + ε ≤ t := by
        by_contra hNotFar
        have htNear : t < τ + ε := lt_of_not_ge hNotFar
        exact (not_lt_of_ge (hGerm t htGt htNear)) htCross
      exact ENNReal.coe_le_coe.mpr htFar
    · subst t
      simp [hContact] at htCross
  have hContradiction : ((τ + ε : ℝ≥0) : ℝ≥0∞) ≤ (τ : ℝ≥0∞) := by
    calc
      ((τ + ε : ℝ≥0) : ℝ≥0∞) ≤
          (⨅ (t : ℝ≥0) (_ : f t < b), (t : ℝ≥0∞)) := hClockBound
      _ = (τ : ℝ≥0∞) := hτ.symm
  exact (not_lt_of_ge hContradiction) hτLt
