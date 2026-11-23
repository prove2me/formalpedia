-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.qQHerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:29.057835+00:00
-- url     : https://prove2.me/submissions/4d3fe569-f576-4224-aead-3ea4a6c9741c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_t22
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_t21
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_t12
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_t11

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
theorem _root_.solution : QQHerm := by
  intro P _ Y
  unfold QQr
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, star_t11, star_t12, star_t21, star_t22]
end Formalism.FourierDecayAlt.P.Mx5
