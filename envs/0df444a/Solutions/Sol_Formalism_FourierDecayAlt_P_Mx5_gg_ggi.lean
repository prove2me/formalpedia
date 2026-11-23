-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.gg_ggi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:34.941042+00:00
-- url     : https://prove2.me/submissions/17c70388-17df-423d-9ce0-a9c7b78d3a55

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
theorem _root_.solution : ggA P * ggiA P = 1 := by
  obtain ⟨-, -, -, -, -, -, h, -, -⟩ := level_function_relations P; exact h
end Formalism.FourierDecayAlt.P.Mx5
