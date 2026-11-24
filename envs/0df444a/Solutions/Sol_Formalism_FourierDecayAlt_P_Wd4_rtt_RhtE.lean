-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.rtt_RhtE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:27.033879+00:00
-- url     : https://prove2.me/submissions/a1a67dae-4ce7-4804-9779-41e29e501f5f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_kronecker_E1_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_eval_two_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_rtt_QE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K B : Type} [Field K] [Ring B] [Algebra K B]
variable {e : Fin 2 → Fin 2 → B}
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution (he : MU e) (Yb Y Y' : K) : RTTat (fun Y => RhtE e (Yb - Y)) Y Y' := by
  have h := rtt_QE he (Yb - Y') (Yb - Y)
  rw [sub_sub_sub_cancel_left] at h
  unfold RTTat RhtE
  simp only [kronecker_E1_smul, eval_two_smul, mul_smul_comm, smul_mul_assoc]
  rw [h, smul_comm]
end Formalism.FourierDecayAlt.P.Wd4
