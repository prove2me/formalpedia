-- Prove2me | solution 1 for D1Bound5.exists_aligned_square_roots
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:44.453554+00:00
-- url     : https://prove2.me/submissions/b6c8b955-26c9-40ec-b537-9479bc531d34

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_exists_sign_root_perturbation

section
namespace D1Bound5



/-- Choose auxiliary square roots of b,c aligned with a fixed root of
bc+1. This is the first estimate in the C>=4 tail proof. -/
theorem _root_.solution (b c r : ℂ)
    (hr : r^2 = b*c+1) (hB : 3 ≤ ‖b‖) (hC : 4 ≤ ‖c‖) :
    ∃ beta gamma : ℂ, beta^2 = b ∧ gamma^2 = c ∧
      (39/20 : ℝ)*‖beta‖*‖gamma‖*‖r-beta*gamma‖ < 1 := by
  obtain ⟨beta,hbeta⟩ := IsAlgClosed.exists_pow_nat_eq b (by decide : 0 < 2)
  obtain ⟨gamma,hgamma⟩ := IsAlgClosed.exists_pow_nat_eq c (by decide : 0 < 2)
  have hbetaN : ‖beta‖^2 = ‖b‖ := by rw [← norm_pow,hbeta]
  have hgammaN : ‖gamma‖^2 = ‖c‖ := by rw [← norm_pow,hgamma]
  have hmul : 12 ≤ ‖b‖*‖c‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hC)]
  have htN : ‖beta*gamma‖^2 = ‖b‖*‖c‖ := by
    rw [norm_mul,mul_pow,hbetaN,hgammaN]
  have ht : beta*gamma ≠ 0 := by
    intro h
    rw [h,norm_zero,zero_pow (by decide : 2 ≠ 0)] at htN
    linarith
  have he : r^2-(beta*gamma)^2 = 1 := by
    rw [hr,mul_pow,hbeta,hgamma]
    ring
  have herr : ‖r^2-(beta*gamma)^2‖ ≤ 1 := by rw [he,norm_one]
  have hgap : 1 < (1-(19/20 : ℝ)^2)*‖beta*gamma‖^2 := by
    rw [htN]
    nlinarith only [hmul]
  obtain ⟨v,hv,H⟩ := exists_sign_root_perturbation r (beta*gamma) (19/20) 1 ht
    (by norm_num) (by norm_num) herr hgap
  norm_num only [norm_mul] at H
  rcases hv with rfl | rfl
  · exact ⟨beta,gamma,hbeta,hgamma,by nlinarith only [H]⟩
  · refine ⟨beta,-gamma,hbeta,by simpa only [neg_sq] using hgamma,?_⟩
    have hdist : ‖r-beta*(-gamma)‖ = ‖-r-beta*gamma‖ := by
      have hid : r-beta*(-gamma) = -(-r-beta*gamma) := by ring
      rw [hid,norm_neg]
    rw [norm_neg,hdist]
    nlinarith only [H]

end D1Bound5
end
