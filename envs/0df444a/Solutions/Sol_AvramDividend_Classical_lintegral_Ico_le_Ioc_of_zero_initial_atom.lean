-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_Ico_le_Ioc_of_zero_initial_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:53:29.419027+00:00
-- url     : https://prove2.me/submissions/af0eb92b-88d6-4942-97c1-95124183f3e2

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-! A zero initial atom allows a half-open prefix to be controlled by (0,t]. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (t : ℝ)
    (hzero : μ ({0} : Set ℝ) = 0) :
    (∫⁻ r in Ico (0 : ℝ) t, f r ∂μ) ≤
      (∫⁻ r in Ioc (0 : ℝ) t, f r ∂μ) := by
  have hs : Ico (0 : ℝ) t ⊆ Ioc (0 : ℝ) t ∪ ({0} : Set ℝ) := by
    intro r hr
    rcases hr with ⟨hr0, hrt⟩
    by_cases heq : r = 0
    · exact Or.inr (by simp [heq])
    · exact Or.inl ⟨lt_of_le_of_ne hr0 (Ne.symm heq), le_of_lt hrt⟩
  calc
    (∫⁻ r in Ico (0 : ℝ) t, f r ∂μ) ≤
        (∫⁻ r in Ioc (0 : ℝ) t ∪ ({0} : Set ℝ), f r ∂μ) :=
          lintegral_mono_set hs
    _ ≤ (∫⁻ r in Ioc (0 : ℝ) t, f r ∂μ) +
          (∫⁻ r in ({0} : Set ℝ), f r ∂μ) :=
            lintegral_union_le f (Ioc (0 : ℝ) t) ({0} : Set ℝ)
    _ = (∫⁻ r in Ioc (0 : ℝ) t, f r ∂μ) := by
      rw [setLIntegral_measure_zero ({0} : Set ℝ) f hzero, add_zero]
