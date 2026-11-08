-- Prove2me | solution 1 for FreedmanTail.lemma_3_1_g_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:26:10.651629+00:00
-- url     : https://prove2.me/submissions/b2f67de6-d9cf-4152-a75b-f10e1f9e8c18

import Mathlib
import Definitions.Def_FreedmanTail_gFun

open FreedmanTail in
theorem solution : StrictMono gFun := by
  have key : ∀ x, gFun x = ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp (t * x) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp only [mul_zero, Real.exp_zero, mul_one]
      have hF : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - t) t := by
        intro t _
        have := (hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)
        refine this.congr_deriv ?_
        push_cast
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        ((by fun_prop : Continuous fun t : ℝ => 1 - t).intervalIntegrable _ _)]
      unfold gFun
      rw [if_pos rfl]
      norm_num
    · have hE : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (t * x)) (Real.exp (t * x) * x) t := by
        intro t
        have := ((hasDerivAt_id t).mul_const x).exp
        simpa using this
      have hF : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
          (fun t : ℝ => (1 - t) * Real.exp (t * x) / x + Real.exp (t * x) / x ^ 2)
          ((1 - t) * Real.exp (t * x)) t := by
        intro t _
        have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
          simpa using (hasDerivAt_id t).const_sub 1
        have := ((h1.mul (hE t)).div_const x).add ((hE t).div_const (x ^ 2))
        refine this.congr_deriv ?_
        field_simp <;> ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        ((by fun_prop : Continuous fun t : ℝ => (1 - t) * Real.exp (t * x)).intervalIntegrable _ _)]
      unfold gFun
      rw [if_neg hx]
      simp only [sub_self, zero_mul, zero_div, zero_add, one_mul, Real.exp_zero, sub_zero]
      field_simp <;> ring
  intro x y hxy
  rw [key, key]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
  · exact (by fun_prop : Continuous fun t : ℝ => (1 - t) * Real.exp (t * x)).continuousOn
  · exact (by fun_prop : Continuous fun t : ℝ => (1 - t) * Real.exp (t * y)).continuousOn
  · intro t ht
    apply mul_le_mul_of_nonneg_left _ (by linarith [ht.2])
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy.le ht.1.le)
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    exact Real.exp_lt_exp.mpr (by linarith)
