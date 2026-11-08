-- Prove2me | solution 1 for FreedmanTail.corollary_3_2_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:29:30.576586+00:00
-- url     : https://prove2.me/submissions/1110a2cd-824f-428e-8e4f-2790314b29c9

import Mathlib
import Definitions.Def_FreedmanTail_eFun

namespace Aux_FreedmanTail_corollary_3_2_exp_bound

lemma I_eq (x : ℝ) (hx : x ≠ 0) :
    ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp (t * x) = (Real.exp x - 1 - x) / x ^ 2 := by
  have hE : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (t * x)) (Real.exp (t * x) * x) t := by
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
  simp only [sub_self, zero_mul, zero_div, zero_add, one_mul, Real.exp_zero, sub_zero]
  field_simp <;> ring

lemma key (y : ℝ) :
    Real.exp y - 1 - y = y ^ 2 * ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp (t * y) := by
  by_cases hy : y = 0
  · subst hy; simp
  · rw [I_eq y hy, mul_div_cancel₀ _ (pow_ne_zero 2 hy)]

lemma I_mono {a b : ℝ} (hab : a ≤ b) :
    ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp (t * a) ≤
      ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp (t * b) := by
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact (by fun_prop : Continuous fun t : ℝ => (1 - t) * Real.exp (t * a)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun t : ℝ => (1 - t) * Real.exp (t * b)).intervalIntegrable _ _
  · intro t ht
    apply mul_le_mul_of_nonneg_left _ (by linarith [ht.2])
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab ht.1)

end Aux_FreedmanTail_corollary_3_2_exp_bound

open FreedmanTail Aux_FreedmanTail_corollary_3_2_exp_bound in
theorem solution {l x : ℝ} (hl : 0 ≤ l) (hx : x ≤ 1) :
    Real.exp (l * x) ≤ 1 + l * x + x ^ 2 * eFun l := by
  have hlx : l * x ≤ l := by nlinarith
  have h1 := key (l * x)
  have h2 := key l
  have hm := I_mono hlx
  have hsq : 0 ≤ (l * x) ^ 2 := sq_nonneg _
  have h3 := mul_le_mul_of_nonneg_left hm hsq
  unfold eFun
  have e : x ^ 2 * (Real.exp l - 1 - l) =
      (l * x) ^ 2 * ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp (t * l) := by
    rw [h2]; ring
  linarith
