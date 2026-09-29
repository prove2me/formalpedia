-- Prove2me | solution 1 for BookProof.ChapterH1.phi_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:41:58.927899+00:00
-- url     : https://prove2.me/submissions/b3214b59-37ec-4561-be00-a87bfe51c4c5

import Definitions.Def_ChapterH1
open BookProof.ChapterH1 intervalIntegral MeasureTheory
set_option autoImplicit false

theorem solution (k : ℕ) : phi k 0 = 1 / k.factorial := by
  cases k with
  | zero => simp [phi]
  | succ k =>
    simp only [phi, mul_zero, Complex.exp_zero, one_mul]
    have hd (x : ℝ) : HasDerivAt
        (fun s : ℝ => -((1 - (s : ℂ)) ^ (k + 1)) / ((k + 1).factorial : ℂ))
        ((1 - (x : ℂ)) ^ k / (k.factorial : ℂ)) x := by
      have h := ((((hasDerivAt_const x (1 : ℂ)).sub
        (hasDerivAt_id x).ofReal_comp).pow (k + 1)).neg).div_const ((k + 1).factorial : ℂ)
      have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      convert h using 1 <;> first | rfl | (simp [Nat.factorial_succ] <;> field_simp <;> ring)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (show IntervalIntegrable (fun s : ℝ => (1 - (s : ℂ)) ^ k / (k.factorial : ℂ)) volume 0 1 from
        Continuous.intervalIntegrable (by fun_prop) _ _)
    simpa [div_eq_mul_inv] using h
#print axioms solution
