-- Prove2me | solution 1 for BranchSummability.gaussian_summable_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:58:13.615673+00:00
-- url     : https://prove2.me/submissions/f6b8f38e-9882-44c4-ad56-c8d59cf3a5f2

import Mathlib
open Real
namespace BranchSummability
 theorem gaussian_resolvent_bound (g t : ℝ) (ht : 0 < t) :
    Real.exp (-g^2*t) ≤ (1+t⁻¹)/(1+g^2) := by
  have hg : 0 ≤ g^2 := sq_nonneg g
  have hd : 0 < 1+g^2 := by positivity
  have he := Real.add_one_le_exp (g^2*t)
  have hi : 0 < t⁻¹ := inv_pos.mpr ht
  have hm : 1+g^2 ≤ (1+t⁻¹)*Real.exp (g^2*t) := by
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1+t⁻¹)
    have hid : (1+t⁻¹)*(g^2*t+1) = 1+g^2+g^2*t+t⁻¹ := by
      field_simp
      <;> ring
    rw [hid] at hmul
    nlinarith [mul_nonneg hg ht.le]
  rw [show -g^2*t = -(g^2*t) by ring, Real.exp_neg, ← one_div]
  exact (div_le_div_iff₀ (Real.exp_pos _) hd).2 (by simpa using hm)
 theorem gaussian_summable_of_resolvent (gamma : ℕ → ℝ)
    (h : Summable (fun j => (1+(gamma j)^2)⁻¹))
    (t : ℝ) (ht : 0 < t) :
    Summable (fun j => Real.exp (-(gamma j)^2*t)) := by
  apply (h.mul_left (1+t⁻¹)).of_nonneg_of_le
  · intro j; exact (Real.exp_pos _).le
  · intro j
    simpa only [div_eq_mul_inv] using gaussian_resolvent_bound (gamma j) t ht
end BranchSummability

theorem solution (gamma : ℕ → ℝ)
    (h : Summable (fun j => (1+(gamma j)^2)⁻¹))
    (t : ℝ) (ht : 0 < t) :
    Summable (fun j => Real.exp (-(gamma j)^2*t)) := by
  exact @BranchSummability.gaussian_summable_of_resolvent gamma h t ht
