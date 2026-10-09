-- Prove2me | solution 1 for BookProof.ChapterGaugeMechanicsCharge.chargeQ_comm_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:34:54.768017+00:00
-- url     : https://prove2.me/submissions/34936e5f-6910-42f0-9545-179675620461

-- Generated from ChapterGaugeMechanicsCharge.lean — solution of BookProof.ChapterGaugeMechanicsCharge.chargeQ_comm_mul
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
import Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_chargeQ_eq_euler
import Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_euler_comm_mul
open BookProof.ChapterGaugeMechanicsCharge





open MvPolynomial

set_option maxHeartbeats 1000000 in
theorem solution (g p : P) :
    chargeQ (g * p) - g * chargeQ p = (-Complex.I) • (eulerOp g * p) := by

  have hc := euler_comm_mul g p
  rw [chargeQ_eq_euler, chargeQ_eq_euler]
  rw [show eulerOp (g * p) = g * eulerOp p + eulerOp g * p by linear_combination hc]
  simp only [smul_add, mul_add, mul_smul_comm]
  module
