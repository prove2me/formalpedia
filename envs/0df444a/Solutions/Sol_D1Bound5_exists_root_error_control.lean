-- Prove2me | solution 1 for D1Bound5.exists_root_error_control
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:55.526625+00:00
-- url     : https://prove2.me/submissions/6d845fa5-aba9-4563-b47e-27ffca4dbe0d

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






/-- Uniform sign selection with a free margin c. The two inequalities
are polynomial inequalities in real norms, without division by a
possibly zero chosen square root. -/
theorem _root_.solution (x t : ℂ) (c : ℝ)
    (hc : 0 ≤ c) (hx : 0 < ‖x‖)
    (hgap : 1 < (1-c^2)*‖x‖) (ht : t^2 = x*(x+1)) :
    ∃ v : ℂ, (v = t ∨ v = -t) ∧
      (1+c)*‖v-x‖ < 1 ∧
      (2*‖x‖*(1+c)^2)*‖(v-x)-(1/2 : ℂ)‖ < 1 := by
  have hxne : x ≠ 0 := norm_pos_iff.mp hx
  have hmarg : 0 < ((1-c^2)*‖x‖-1)*‖x‖ :=
    mul_pos (sub_pos.mpr hgap) hx
  have hgap' : ‖x‖ < (1-c^2)*‖x‖^2 := by
    nlinarith only [hmarg]
  have hdiff : t^2-x^2 = x := by rw [ht]; ring
  have herr : ‖t^2-x^2‖ ≤ ‖x‖ := by rw [hdiff]
  obtain ⟨v,hv,hnear⟩ := exists_sign_root_perturbation
    t x c ‖x‖ hxne hc hx herr hgap'
  have hsmall : (1+c)*‖v-x‖ < 1 := by
    by_contra h
    have hh : 1 ≤ (1+c)*‖v-x‖ := le_of_not_gt h
    have hm := mul_nonneg hx.le (sub_nonneg.mpr hh)
    nlinarith only [hnear,hm]
  have hv2 : v^2 = x*(x+1) := by
    rcases hv with h | h
    · rw [h]; exact ht
    · rw [h]; simpa only [neg_sq] using ht
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
  have hep : 0 ≤ ‖e‖ := norm_nonneg _
  have hcp : 0 < 1+c := by linarith
  have hpp : 0 ≤ (1+c)*‖e‖ := mul_nonneg hcp.le hep
  have hsquare : ((1+c)*‖e‖)^2 < 1 := by
    nlinarith only [hsmall,hpp]
  have hsquare' : (1+c)^2*‖e‖^2 < 1 := by
    nlinarith only [hsquare]
  have hnormfactor : (2*‖x‖*(1+c)^2)*(‖e‖^2/(2*‖x‖)) =
      (1+c)^2*‖e‖^2 := by
    field_simp [show (2:ℝ)*‖x‖ ≠ 0 by positivity]
    <;> ring
  have hbound : (2*‖x‖*(1+c)^2)*‖e-(1/2 : ℂ)‖ < 1 := by
    rw [hnorm,hnormfactor]
    exact hsquare'
  exact ⟨v,hv,by simpa only [e] using hsmall,by simpa only [e] using hbound⟩





end D1Bound5
end
