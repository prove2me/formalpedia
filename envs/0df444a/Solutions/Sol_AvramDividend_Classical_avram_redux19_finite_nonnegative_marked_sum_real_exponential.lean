-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_finite_nonnegative_marked_sum_real_exponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:43:31.575786+00:00
-- url     : https://prove2.me/submissions/3302695e-7817-4c6d-b148-fa0947c8322e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section

/-! Convert a finite nonnegative ENNReal mark sum to the real exponential. -/
theorem solution
    {α : Type*} (S : Finset α) (a : α → ℝ)
    (ha : ∀ u ∈ S, 0 ≤ a u) :
    Real.exp (-(∑ u ∈ S, ENNReal.ofReal (a u)).toReal) =
      Real.exp (∑ u ∈ S, -a u) := by
  have hfinite : ∀ u ∈ S, ENNReal.ofReal (a u) ≠ ⊤ := by
    intro u hu
    exact ENNReal.ofReal_ne_top
  have hsum := ENNReal.toReal_sum (s := S)
    (f := fun u => ENNReal.ofReal (a u)) hfinite
  rw [hsum]
  have hpoint : (∑ u ∈ S, (ENNReal.ofReal (a u)).toReal) =
      ∑ u ∈ S, a u := by
    apply Finset.sum_congr rfl
    intro u hu
    exact ENNReal.toReal_ofReal (ha u hu)
  rw [hpoint]
  simp only [Finset.sum_neg_distrib]
