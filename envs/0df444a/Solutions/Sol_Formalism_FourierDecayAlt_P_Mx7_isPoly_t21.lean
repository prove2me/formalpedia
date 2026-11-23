-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.isPoly_t21
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:59.832519+00:00
-- url     : https://prove2.me/submissions/a8547766-8794-4cd5-af86-c38e26152632

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_xA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_lowering_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_S21
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul


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
theorem _root_.solution (P : Par) : IsPoly (t21 P) :=
  (((IsPoly.const (ggA P)).mul (isPoly_xA P)).mul (isPoly_lowering_constant P)).add (isPoly_S21 P)
end Formalism.FourierDecayAlt.P.Mx7
