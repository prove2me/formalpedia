-- Prove2me | solution 1 for BookProof.ChapterGaugeMechanicsCharge.euler_comm_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:34:56.824995+00:00
-- url     : https://prove2.me/submissions/382f3f3c-2387-4526-b962-290bdedaba28

-- Generated from ChapterGaugeMechanicsCharge.lean — solution of BookProof.ChapterGaugeMechanicsCharge.euler_comm_bilinear
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
import Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_pderiv_comm_core
open BookProof.ChapterGaugeMechanicsCharge





open MvPolynomial

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin 2) (p : P) :
    eulerOp (X j * pderiv k p) = X j * pderiv k (eulerOp p) := by

  have hc : ∀ a b : Fin 2, pderiv a (pderiv b p) = pderiv b (pderiv a p) :=
    fun a b => pderiv_comm_core a b p
  fin_cases j <;> fin_cases k <;>
    simp [eulerOp_apply,
      pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
      pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), hc 0 1] <;> ring
