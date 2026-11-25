-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.blockSchur_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:33:19.088374+00:00
-- url     : https://prove2.me/submissions/56ce2c60-b73e-4ced-b7ee-4b0a9da29e5d

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_block_cross_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution : KB.BlockSchur := by
  intro ι α β _ Y₁ Y₂ κa κw κb a w b hκ hv
  exact block_cross_le (blockPSD_mul hκ (blockPSD_prod Finset.univ a w b (fun v _ => hv v)))
end Formalism.FourierDecayAlt.P.PBA
