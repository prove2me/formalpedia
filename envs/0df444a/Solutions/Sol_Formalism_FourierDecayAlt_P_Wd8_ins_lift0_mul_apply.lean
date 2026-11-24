-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.ins_lift0_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:32.106031+00:00
-- url     : https://prove2.me/submissions/a0379919-2140-4643-8d8f-eda9c9cc68b6

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (a : S) (M : M2 A) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((ins a (lift0 M) : SlopeTestRemainingChoices S A) * B) x y = ∑ j, M (x a) j * B (Function.update x a j) y := by
  unfold ins
  simp only [Finset.sum_mul, Matrix.sum_apply, mul_assoc, eU_mul_apply, lift0, Matrix.map_apply,
    io_mul_apply]
  rw [Finset.sum_comm]
  simp
end Formalism.FourierDecayAlt.P.Wd8
