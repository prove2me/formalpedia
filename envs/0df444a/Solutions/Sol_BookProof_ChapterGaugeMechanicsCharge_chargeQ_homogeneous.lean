-- Prove2me | solution 1 for BookProof.ChapterGaugeMechanicsCharge.chargeQ_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:34:25.621639+00:00
-- url     : https://prove2.me/submissions/7647ddc7-16d8-4f45-a3fb-0fe4f1a14b8a

-- Generated from ChapterGaugeMechanicsCharge.lean — solution of BookProof.ChapterGaugeMechanicsCharge.chargeQ_homogeneous
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
import Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_chargeQ_eq_euler
open BookProof.ChapterGaugeMechanicsCharge





open MvPolynomial

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} {p : P} (hp : p.IsHomogeneous n) :
    chargeQ p = (-Complex.I * (n + 2)) • p := by

  have hE : eulerOp p = (n : ℂ) • p := by
    have h := hp.sum_X_mul_pderiv
    rw [Fin.sum_univ_two] at h
    rw [eulerOp_apply, h, MvPolynomial.smul_eq_C_mul]
    simp [nsmul_eq_mul]
  rw [chargeQ_eq_euler, hE]
  module
