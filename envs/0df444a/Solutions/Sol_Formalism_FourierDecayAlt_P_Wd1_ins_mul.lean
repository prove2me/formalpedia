-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd1.ins_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:56.782245+00:00
-- url     : https://prove2.me/submissions/978fa7c4-b480-4306-8ea1-dd3e006a30f1

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_mul_eU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd1
theorem _root_.solution (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) :
    ins a (M * N) = ins a M * ins a N := by
  have key : ∀ i j k l : Fin 2, (eU a i j : SlopeTestRemainingChoices S A) * M i j * (eU a k l * N k l) =
      if j = k then eU a i l * (M i j * N k l) else 0 := by
    intro i j k l
    have e1 : (eU a i j : SlopeTestRemainingChoices S A) * M i j * (eU a k l * N k l) =
        eU a i j * (M i j * eU a k l) * N k l := by
      simp only [mul_assoc]
    rw [e1, ← (hM i j k l).eq]
    have e2 : (eU a i j : SlopeTestRemainingChoices S A) * (eU a k l * M i j) * N k l =
        (eU a i j * eU a k l) * (M i j * N k l) := by
      simp only [mul_assoc]
    rw [e2, eU_mul_eU]
    split_ifs <;> simp
  simp only [ins, Fin.sum_univ_two, Matrix.mul_apply, add_mul, mul_add, key]
  simp
  abel
end Formalism.FourierDecayAlt.P.Wd1
