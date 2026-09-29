-- Prove2me | solution 1 for BookProof.ChapterH1.phi_succ_mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:41:59.690984+00:00
-- url     : https://prove2.me/submissions/cb85907b-c710-4ffb-9614-1c1bf2167b65

import Definitions.Def_ChapterH1
open BookProof.ChapterH1 intervalIntegral MeasureTheory
set_option autoImplicit false

theorem solution (k : ℕ) (z : ℂ) : z * phi (k + 1) z = phi k z - 1 / k.factorial := by
  have he (x : ℝ) : HasDerivAt (fun s : ℝ => Complex.exp (s * z))
      (Complex.exp (x * z) * z) x := by
    simpa using (((hasDerivAt_id x).ofReal_comp).mul_const z).cexp
  cases k with
  | zero =>
    simp only [phi, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    rw [← intervalIntegral.integral_const_mul]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => he x)
      (show IntervalIntegrable (fun s : ℝ => Complex.exp (s * z) * z) volume 0 1 from
        Continuous.intervalIntegrable (by fun_prop) _ _)
    simpa [mul_comm] using h
  | succ k =>
    have hd (x : ℝ) : HasDerivAt
        (fun s : ℝ => Complex.exp (s * z) * (1 - (s : ℂ)) ^ (k + 1) /
          ((k + 1).factorial : ℂ))
        (z * (Complex.exp (x * z) * (1 - (x : ℂ)) ^ (k + 1) / ((k + 1).factorial : ℂ)) -
          Complex.exp (x * z) * (1 - (x : ℂ)) ^ k / (k.factorial : ℂ)) x := by
      have hp := ((hasDerivAt_const x (1 : ℂ)).sub (hasDerivAt_id x).ofReal_comp).pow (k + 1)
      have hh := ((he x).mul hp).div_const ((k + 1).factorial : ℂ)
      have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      convert hh using 1 <;> first | rfl | (simp [Nat.factorial_succ] <;> field_simp <;> ring)
    have hi1 : IntervalIntegrable (fun s : ℝ => z *
        (Complex.exp (s * z) * (1 - (s : ℂ)) ^ (k + 1) / ((k + 1).factorial : ℂ))) volume 0 1 :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have hi2 : IntervalIntegrable (fun s : ℝ =>
        Complex.exp (s * z) * (1 - (s : ℂ)) ^ k / (k.factorial : ℂ)) volume 0 1 :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hi1.sub hi2)
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul] at h
    have hrel : z * phi (k + 2) z - phi (k + 1) z = -(1 / ((k + 1).factorial : ℂ)) := by
      simpa [phi] using h
    change z * phi (k + 2) z = phi (k + 1) z - 1 / ((k + 1).factorial : ℂ)
    calc
      _ = -(1 / ((k + 1).factorial : ℂ)) + phi (k + 1) z := sub_eq_iff_eq_add.mp hrel
      _ = _ := by ring
#print axioms solution
