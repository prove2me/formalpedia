-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.isPoly_S21
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:21.6535+00:00
-- url     : https://prove2.me/submissions/0a6688d9-c610-4483-a0e3-c44103b8dfe9

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_xEx
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_sum


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
theorem _root_.solution (P : Par) : IsPoly (weightedSumBis P) :=
  IsPoly.sum _ _ fun l _ => (IsPoly.const (SS P l)).mul (isPoly_xEx P {l})
end Formalism.FourierDecayAlt.P.Mx7
