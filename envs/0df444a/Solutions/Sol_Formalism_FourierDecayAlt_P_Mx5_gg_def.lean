-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.gg_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:35.56683+00:00
-- url     : https://prove2.me/submissions/157cbad4-5fa5-49f4-bef8-489906163ec4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_level_function_relations


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution : ggA P = zA P * zbA P - algebraMap ℂ (A P) (P.TT : ℂ) := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := level_function_relations P; exact h
end Formalism.FourierDecayAlt.P.Mx5
