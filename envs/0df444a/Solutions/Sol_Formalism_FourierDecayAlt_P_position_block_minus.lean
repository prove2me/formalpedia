-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.position_block_minus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:13.422643+00:00
-- url     : https://prove2.me/submissions/0dec194d-4796-46f7-b341-7c7870f72d29

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_blk_minus
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_Rht0_mul_apply
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
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.TransposedCoordinateBlockCondition := by
  intro A S _ _ _ _ _ b M d i j
  have e : Formalism.YangianSpanCharacter.F.blk (((d - 1)⁻¹ • pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) -
      Pf (SlopeTestRemainingChoices S A))) * E1 M) i j =
      Matrix.of fun k l => (d - 1)⁻¹ • (d • (if k = l then M i j else 0) - (if k = i then M l j else 0)) := by
    ext k l
    have := Fr4.blk_minus M d i j k l
    simp only [eq_comm (a := i) (b := k)] at this
    exact congrFun (congrFun this _) _
  rw [e, Fr4.ins_block b _ d (M i j) (fun l => M l j) i, Fr4.Rht0_mul_apply]
end Formalism.FourierDecayAlt.P
