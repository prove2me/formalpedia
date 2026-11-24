-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.start_module_assemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:25.573716+00:00
-- url     : https://prove2.me/submissions/3ea99f1e-a868-4676-ad33-8e146bcbf8fd

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_isStart_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_sgn_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_sgn_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_qC_real

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
theorem _root_.solution : Formalism.FourierDecayAlt.M.StartIsStartAssemble := by
  intro hH hR hD P hP l
  exact Mx8.isStart_smul (QQr P) (qC P) (sgn P l) (Mx8.sgn_sq P l) (Mx8.sgn_star P l)
    ⟨fun Y hY => by rw [hH P hP Y, hY], hR P hP, hD P hP, Mx8.qC_real P⟩
end Formalism.FourierDecayAlt.P
