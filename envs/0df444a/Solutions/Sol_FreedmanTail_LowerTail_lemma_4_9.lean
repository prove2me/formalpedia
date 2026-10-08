-- Prove2me | solution 1 for FreedmanTail.LowerTail.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:29:58.582275+00:00
-- url     : https://prove2.me/submissions/4ad70314-ca12-433f-8394-da3c93b63a87

import Mathlib

/-- Freedman (1975), (4.9) Lemma, p. 109: if `α > 0` and `x > 2 log α`, then `e^x > αx`. -/
theorem solution (α x : ℝ) (hα : 0 < α) (hx : 2 * Real.log α < x) :
    α * x < Real.exp x := by
  by_cases hx0 : x ≤ 0
  · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos hα.le hx0) (Real.exp_pos x)
  have hxpos : 0 < x := lt_of_not_ge hx0
  have ha : α < Real.exp (x / 2) := by
    rw [← Real.exp_log hα]
    apply Real.exp_lt_exp.mpr
    linarith
  have he := Real.add_one_lt_exp (show x / 4 ≠ 0 by linarith)
  have hep := Real.exp_pos (x / 4)
  have hxx : x < Real.exp (x / 2) := by
    have heq : Real.exp (x / 2) = Real.exp (x / 4) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1 <;> ring
    rw [heq]
    nlinarith [sq_nonneg (x / 4 - 1)]
  calc
    α * x < Real.exp (x / 2) * Real.exp (x / 2) := mul_lt_mul ha hxx.le hxpos (Real.exp_pos _).le
    _ = Real.exp x := by rw [← Real.exp_add]; congr 1 <;> ring


#print axioms solution
