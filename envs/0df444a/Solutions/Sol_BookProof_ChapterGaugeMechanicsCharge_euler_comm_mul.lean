-- Prove2me | solution 1 for BookProof.ChapterGaugeMechanicsCharge.euler_comm_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:34:38.700985+00:00
-- url     : https://prove2.me/submissions/a49142d7-da97-4836-acdf-be4b83461518

-- Generated from ChapterGaugeMechanicsCharge.lean — solution of BookProof.ChapterGaugeMechanicsCharge.euler_comm_mul
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
open BookProof.ChapterGaugeMechanicsCharge





open MvPolynomial

set_option maxHeartbeats 1000000 in
theorem solution (g p : P) :
    eulerOp (g * p) - g * eulerOp p = (eulerOp g) * p := by

  simp only [eulerOp_apply, pderiv_mul]
  ring
