-- Prove2me | solution 1 for AvramDividend.Classical.exponential_decay_difference_le_interval_length
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:31:37.376566+00:00
-- url     : https://prove2.me/submissions/ed90570d-a225-4c99-84e6-9adbf8784198

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- On nonnegative arguments the decreasing exponential has Lipschitz constant one. -/
theorem solution (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-a) - Real.exp (-b) ≤ b - a := by
  have hdelta : 0 ≤ b - a := sub_nonneg.mpr hab
  have hbound : 1 - Real.exp (-(b - a)) ≤ b - a := by
    have h := Real.one_sub_le_exp_neg (b - a)
    linarith
  have hexp : Real.exp (-a) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hnonneg : 0 ≤ 1 - Real.exp (-(b - a)) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hdelta)
  have hprod :
      Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤ b - a := by
    calc
      _ ≤ 1 * (1 - Real.exp (-(b - a))) :=
        mul_le_mul_of_nonneg_right hexp hnonneg
      _ = 1 - Real.exp (-(b - a)) := one_mul _
      _ ≤ b - a := hbound
  have hfactor :
      Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    calc
      Real.exp (-b) = Real.exp (-a + -(b - a)) := by congr 1; ring
      _ = Real.exp (-a) * Real.exp (-(b - a)) := Real.exp_add _ _
  rw [hfactor]
  nlinarith [hprod]
