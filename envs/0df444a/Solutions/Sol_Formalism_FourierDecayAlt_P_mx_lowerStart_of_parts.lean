-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.mx_lowerStart_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:51.155802+00:00
-- url     : https://prove2.me/submissions/32d685e3-dc4d-4cab-a221-2a390de91f3a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_lowerStart_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_start_module_assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (hH : Formalism.FourierDecayAlt.M.QQHerm) (hR : Formalism.FourierDecayAlt.M.QQRTT) (hD : Formalism.FourierDecayAlt.M.QQDet) :
    Formalism.FourierDecayAlt.M.LowerStart := by
  exact Mx8.lowerStart_of (start_module_assemble hH hR hD)
end Formalism.FourierDecayAlt.P
