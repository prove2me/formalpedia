-- Prove2me | solution 1 for BBPSSW.Distill.singlet_bilateral_invariant
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:31:02.626072+00:00
-- url     : https://prove2.me/submissions/86ca5084-88d1-4979-93c4-cb592e89f7ab

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_BBPSSW_Distill_bellVec
import Definitions.Def_BBPSSW_Distill_bilateral

open BBPSSW.Distill in
theorem solution (U : Matrix (Fin 2) (Fin 2) ℂ) :
    QAlgorithms.act (bilateral U) (bellVec .psiMinus) = U.det • bellVec .psiMinus := by
  unfold QAlgorithms.act bilateral bellVec
  ext x
  rcases x with ⟨i, j⟩
  simp only [PiLp.smul_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kronecker_apply, Matrix.det_fin_two,
    smul_eq_mul, PiLp.toLp_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring
