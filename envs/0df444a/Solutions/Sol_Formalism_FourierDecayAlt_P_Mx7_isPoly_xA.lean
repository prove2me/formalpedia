-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.isPoly_xA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:46.059442+00:00
-- url     : https://prove2.me/submissions/36757e6c-d9f6-4dc8-be4b-e5dab706aaf4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xC_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) : IsPoly (xA P) :=
  (isPoly_kap P _).congr (fun Y => congrArg (kap P) (funext fun π => xC_poly P π Y))
end Formalism.FourierDecayAlt.P.Mx7
