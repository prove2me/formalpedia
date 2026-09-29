-- Prove2me | solution 1 for BookProof.ChapterH1.phi_one
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:33:54.626899+00:00
-- url     : https://prove2.me/submissions/a14e04fd-d227-4353-b238-5059d43ec28c

import Definitions.Def_ChapterH1
open BookProof.ChapterH1 intervalIntegral MeasureTheory
set_option autoImplicit false

theorem solution {z : ℂ} (hz : z ≠ 0) : phi 1 z = (Complex.exp z - 1) / z := by
  simp only [phi, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  apply (eq_div_iff hz).mpr
  rw [← intervalIntegral.integral_mul_const]
  have hd (x : ℝ) : HasDerivAt (fun s : ℝ => Complex.exp (s * z))
      (Complex.exp (x * z) * z) x := by
    simpa using (((hasDerivAt_id x).ofReal_comp).mul_const z).cexp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (show IntervalIntegrable (fun s : ℝ => Complex.exp (s * z) * z) volume 0 1 from
      Continuous.intervalIntegrable (by fun_prop) _ _)
  simpa using h
#print axioms solution
