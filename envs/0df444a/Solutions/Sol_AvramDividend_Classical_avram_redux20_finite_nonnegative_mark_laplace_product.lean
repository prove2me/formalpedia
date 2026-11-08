-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux20_finite_nonnegative_mark_laplace_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:18:20.127523+00:00
-- url     : https://prove2.me/submissions/0acd8258-24eb-4cea-abb8-d5a3421f6cff

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! A real Laplace factor for a finite physical mark set is a product. -/
theorem solution
    {α : Type*} (S : Finset α) (a : α → ℝ)
    (ha : ∀ u ∈ S, 0 ≤ a u) :
    Real.exp (-(∑ u ∈ S, ENNReal.ofReal (a u)).toReal) =
      ∏ u ∈ S, Real.exp (-(a u)) := by
  have hfinite : ∀ u ∈ S, ENNReal.ofReal (a u) ≠ ⊤ := by
    intro u hu
    exact ENNReal.ofReal_ne_top
  have hsum := ENNReal.toReal_sum (s := S)
    (f := fun u => ENNReal.ofReal (a u)) hfinite
  rw [hsum]
  have hreal : (∑ u ∈ S, (ENNReal.ofReal (a u)).toReal) =
      ∑ u ∈ S, a u := by
    apply Finset.sum_congr rfl
    intro u hu
    exact ENNReal.toReal_ofReal (ha u hu)
  rw [hreal]
  rw [← Finset.sum_neg_distrib]
  exact Real.exp_sum S (fun u => -(a u))
