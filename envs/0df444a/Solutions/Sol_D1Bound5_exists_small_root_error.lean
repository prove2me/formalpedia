-- Prove2me | solution 1 for D1Bound5.exists_small_root_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:42.680831+00:00
-- url     : https://prove2.me/submissions/b9e8ace2-a274-46c8-ae90-d9c7346381b7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_exists_sign_root_perturbation

section
namespace D1Bound5

/-- A sign of every complex square root of x(x+1), when |x| >= 9,
has correction strictly within 16/31 of zero and 128/8649 of 1/2.
This is the branch-selection part of (integrated-1)--(integrated-2);
the constants are uniform and do not require an analytic square root. -/
theorem _root_.solution (x t : ℂ)
    (hx : 9 ≤ ‖x‖) (ht : t^2 = x*(x+1)) :
    ∃ v : ℂ, (v = t ∨ v = -t) ∧
      ‖v-x‖ < (16/31 : ℝ) ∧
      ‖(v-x)-(1/2 : ℂ)‖ < (128/8649 : ℝ) := by
  have hxpos : 0 < ‖x‖ := by linarith
  have hxne : x ≠ 0 := norm_pos_iff.mp hxpos
  have hxSq : 9*‖x‖ ≤ ‖x‖^2 := by
    nlinarith [mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hx)]
  have hgap : ‖x‖ < (1-(15/16 : ℝ)^2)*‖x‖^2 := by
    nlinarith only [hxSq, hx]
  have hdiff : t^2-x^2 = x := by
    rw [ht]
    ring
  have herr0 : ‖t^2-x^2‖ ≤ ‖x‖ := by rw [hdiff]
  obtain ⟨v,hv,hclose⟩ :=
    exists_sign_root_perturbation t x (15/16) ‖x‖ hxne
      (by norm_num) hxpos herr0 hgap
  have hsmall : ‖v-x‖ < (16/31 : ℝ) := by
    have hlarge : (31/16 : ℝ)*‖x‖*‖v-x‖ < ‖x‖ := by
      convert hclose using 1 <;> norm_num
    have hcancel : ‖x‖ * ((31/16 : ℝ)*‖v-x‖) < ‖x‖ * 1 := by
      nlinarith only [hlarge]
    have H : (31/16 : ℝ)*‖v-x‖ < 1 := by
      by_contra h
      have hh : 1 ≤ (31/16 : ℝ)*‖v-x‖ := le_of_not_gt h
      have hm := mul_nonneg hxpos.le (sub_nonneg.mpr hh)
      nlinarith only [hcancel, hm]
    nlinarith only [H]
  have hv2 : v^2 = x*(x+1) := by
    rcases hv with h | h
    · rw [h]
      exact ht
    · rw [h]
      simpa only [neg_sq] using ht
  let e : ℂ := v-x
  have heq : e^2+2*x*e = x := by
    dsimp only [e]
    calc
      (v-x)^2+2*x*(v-x) = v^2-x^2 := by ring
      _ = x := by rw [hv2]; ring
  have hden : (2:ℂ)*x ≠ 0 := mul_ne_zero (by norm_num) hxne
  have hhalf : e-(1/2 : ℂ) = -e^2/(2*x) := by
    apply (eq_div_iff hden).mpr
    linear_combination heq
  have hnorm : ‖e-(1/2 : ℂ)‖ = ‖e‖^2/(2*‖x‖) := by
    rw [hhalf,norm_div,norm_neg,norm_pow,norm_mul,Complex.norm_two]
  have hsmallE : ‖e‖ < (16/31 : ℝ) := hsmall
  have hEpos : 0 ≤ ‖e‖ := norm_nonneg _
  have hsquare : ‖e‖^2 < (16/31 : ℝ)^2 := by
    nlinarith only [hsmallE, hEpos]
  have hstrict : ‖e‖^2 < (128/8649 : ℝ)*(2*‖x‖) := by
    nlinarith only [hsquare, hx]
  have hbound : ‖e-(1/2 : ℂ)‖ < (128/8649 : ℝ) := by
    rw [hnorm]
    exact (div_lt_iff₀ (by positivity : 0 < 2*‖x‖)).mpr hstrict
  exact ⟨v,hv,hsmall,by simpa only [e] using hbound⟩










end D1Bound5
end
