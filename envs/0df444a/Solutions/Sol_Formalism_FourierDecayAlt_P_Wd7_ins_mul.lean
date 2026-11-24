-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.ins_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:51.186386+00:00
-- url     : https://prove2.me/submissions/a03b676f-898f-425f-854c-6c7b64e5769b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_mul_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_mul_eU


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) :
    ins a (M * N) = ins a M * ins a N := by
  unfold ins
  have key : ∀ i j k l : Fin 2, (eU a i j * M i j) * ((eU a k l : SlopeTestRemainingChoices S A) * N k l) =
      if j = k then eU a i l * (M i j * N k l) else 0 := by
    intro i j k l
    have h := (hM i j k l).eq
    calc (eU a i j * M i j) * ((eU a k l : SlopeTestRemainingChoices S A) * N k l)
        = eU a i j * (M i j * eU a k l) * N k l := by simp only [mul_assoc]
      _ = eU a i j * (eU a k l * M i j) * N k l := by rw [h]
      _ = (eU a i j * eU a k l) * (M i j * N k l) := by simp only [mul_assoc]
      _ = _ := by rw [eU_mul_eU]; split_ifs <;> simp
  simp only [Finset.sum_mul, Finset.mul_sum, key, Matrix.mul_apply]
  simp only [Fin.sum_univ_two]
  simp
  abel
end Formalism.FourierDecayAlt.P.Wd7
