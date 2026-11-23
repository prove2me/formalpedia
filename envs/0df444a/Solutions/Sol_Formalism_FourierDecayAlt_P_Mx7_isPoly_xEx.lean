-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.isPoly_xEx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:46.150337+00:00
-- url     : https://prove2.me/submissions/3ced8991-cb24-4468-b65a-9a5676f5a9ce

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xEx_poly
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
theorem _root_.solution (P : Par) (ex : Finset ℕ) : IsPoly (fun Y => kap P fun π => xEx P ex π Y) :=
  (isPoly_kap P _).congr (fun Y => congrArg (kap P) (funext fun π => xEx_poly P ex π Y))
end Formalism.FourierDecayAlt.P.Mx7
