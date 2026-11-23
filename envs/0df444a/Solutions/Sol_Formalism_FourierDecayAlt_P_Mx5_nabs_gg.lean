-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.nabs_gg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:28.643533+00:00
-- url     : https://prove2.me/submissions/679d9e67-11fd-4c1c-8680-1637d5a5c5f1

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_level_nabla_star_relations


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
theorem _root_.solution : nabsA P * ggA P = ggA P * nabsA P - zA P := by
  obtain ⟨-, -, -, -, h, -, -⟩ := level_nabla_star_relations P; exact h
end Formalism.FourierDecayAlt.P.Mx5
