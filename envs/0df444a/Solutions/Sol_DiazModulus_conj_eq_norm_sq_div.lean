-- Prove2me | solution 1 for DiazModulus.conj_eq_norm_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T06:59:31.874001+00:00
-- url     : https://prove2.me/submissions/0a869173-5a5e-4065-94ba-5acf3f35fb3a

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

open DiazModulus in
theorem solution (u : ℂ) :
    conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 / u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · rw [eq_div_iff hu, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
