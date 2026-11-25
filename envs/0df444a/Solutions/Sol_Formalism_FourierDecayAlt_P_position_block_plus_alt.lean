-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.position_block_plus_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:21.320238+00:00
-- url     : https://prove2.me/submissions/60d9d8c0-7ed9-47df-af05-31d6a04f18e1

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_blk_plus
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_mul_rmatrix_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_ins_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.CoordinateBlockCondition := by
  intro A S _ _ _ _ _ a M D hM i j
  have e : Formalism.YangianSpanCharacter.F.blk (E1 M *
      ((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)))) i j =
      Matrix.of fun k l => (D - 1)⁻¹ • (D • (if k = l then M i j else 0) - (if k = j then M i l else 0)) := by
    ext k l
    exact congrFun (congrFun (Fr4.blk_plus M D i j k l) _) _
  rw [e, Fr4.ins_block a _ D (M i j) (fun l => M i l) j, Fr4.mul_rmatrix_apply, (hM i 0 j 0).eq, (hM i 1 j 1).eq]
end Formalism.FourierDecayAlt.P
