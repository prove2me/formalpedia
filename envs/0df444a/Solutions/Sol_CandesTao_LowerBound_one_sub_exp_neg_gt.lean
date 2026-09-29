-- Prove2me | solution 1 for CandesTao.LowerBound.one_sub_exp_neg_gt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:18:31.173207+00:00
-- url     : https://prove2.me/submissions/df4104ed-7662-4c59-b70e-af9d7813e691

import Mathlib.Analysis.SpecialFunctions.Exp

namespace CandesTao.LowerBound

theorem aux_oseng_key (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) < 1 - x + x ^ 2 / 2 := by
  have h1 : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx.le
  have hprod : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-x) := Real.exp_pos _
  have hx4 : 0 < x ^ 4 := by positivity
  -- (1 - x + x²/2)(1 + x + x²/2) = 1 + x⁴/4
  have hid : (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) = 1 + x ^ 4 / 4 := by ring
  have hq : 0 < 1 + x + x ^ 2 / 2 := by positivity
  by_contra hcon
  rw [not_lt] at hcon
  -- e^{-x} ≥ 1 - x + x²/2, so 1 = e^{-x} e^x ≥ (1 - x + x²/2)(1 + x + x²/2) = 1 + x⁴/4 > 1
  have hA : 0 < 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have : (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul hcon h1 hq.le hpos.le
  rw [hid, hprod] at this
  linarith

end CandesTao.LowerBound

open CandesTao.LowerBound

theorem solution (x : ℝ) (hx : 0 < x) :
    1 - Real.exp (-x) > x - x ^ 2 / 2 := by
  have := aux_oseng_key x hx
  linarith
