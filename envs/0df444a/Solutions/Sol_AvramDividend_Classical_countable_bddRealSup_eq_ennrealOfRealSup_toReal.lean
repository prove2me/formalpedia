-- Prove2me | solution 1 for AvramDividend.Classical.countable_bddRealSup_eq_ennrealOfRealSup_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:53:43.587535+00:00
-- url     : https://prove2.me/submissions/b6e19695-67ce-476c-90bf-ba86b48f3958

import Mathlib.Data.ENNReal.Operations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal

/-- A bounded countable real record including a nonnegative value equals its ENNReal encoding. -/
theorem solution (f : ℕ → ℝ)
    (hb : BddAbove (Set.range f))
    (hzero : 0 ≤ ⨆ i : ℕ, f i) :
    (⨆ i : ℕ, ENNReal.ofReal (f i)).toReal = ⨆ i : ℕ, f i := by
  have hfinite : ∀ i : ℕ, ENNReal.ofReal (f i) ≠ ⊤ := by
    intro i
    exact ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_iSup hfinite]
  have hle : ∀ i : ℕ, f i ≤ (ENNReal.ofReal (f i)).toReal := by
    intro i
    by_cases hi : 0 ≤ f i
    · simp [ENNReal.toReal_ofReal hi]
    · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hi)]
      simpa using (le_of_not_ge hi)
  have hbound : ∀ i : ℕ,
      (ENNReal.ofReal (f i)).toReal ≤ (⨆ j : ℕ, f j) := by
    intro i
    by_cases hi : 0 ≤ f i
    · rw [ENNReal.toReal_ofReal hi]
      exact le_ciSup hb i
    · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hi)]
      simpa using hzero
  have hbDecoded : BddAbove
      (Set.range (fun i : ℕ => (ENNReal.ofReal (f i)).toReal)) := by
    refine ⟨⨆ j : ℕ, f j, ?_⟩
    rintro y ⟨i, rfl⟩
    exact hbound i
  apply le_antisymm
  · exact ciSup_le hbound
  · exact ciSup_le (fun i => (hle i).trans (le_ciSup hbDecoded i))
