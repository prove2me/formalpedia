-- Prove2me | solution 1 for D1Bound5.normalized_root_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:31.746532+00:00
-- url     : https://prove2.me/submissions/91f3a369-7589-4906-8bc7-c4cd0c9e616b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- An elementary root estimate. No analytic branch or power series is
needed: the sign is specified by the nonnegative real part. -/
theorem _root_.solution (q : ℂ) (c rho : ℝ)
    (hc : 0 ≤ c) (hrho : 0 < rho) (hgap : rho < 1-c^2)
    (hRe : 0 ≤ q.re) (hq : ‖q^2-1‖ ≤ rho) :
    (1+c)*‖q-1‖ < rho := by
  have hreal : 1-(q.re*q.re-q.im*q.im) ≤ rho := by
    have h := Complex.re_le_norm (1-q*q)
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re] at h
    have hn : ‖1-q*q‖ = ‖q^2-1‖ := by rw [pow_two, norm_sub_rev]
    rw [hn] at h
    exact h.trans hq
  have hqc : c < q.re := by
    nlinarith [sq_nonneg q.im]
  have hplus : 1+c < ‖q+1‖ := by
    have h := Complex.re_le_norm (q+1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hp : ‖q-1‖*‖q+1‖ ≤ rho := by
    rw [← norm_mul]
    have hid : (q-1)*(q+1) = q^2-1 := by ring
    rwa [hid]
  by_cases hzero : ‖q-1‖ = 0
  · simpa only [hzero, mul_zero] using hrho
  · have hpos : 0 < ‖q-1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith



end D1Bound5
end
