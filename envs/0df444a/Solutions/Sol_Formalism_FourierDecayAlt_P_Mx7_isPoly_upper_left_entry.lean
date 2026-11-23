-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.isPoly_upper_left_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:00.143968+00:00
-- url     : https://prove2.me/submissions/1b010003-7e43-4ed8-b798-52ee50960676

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_w
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_lowering_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_raising_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_S21
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_S12
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_quartic_sum
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
theorem _root_.solution (P : Par) : IsPoly (t11 P) :=
  (((((IsPoly.const (ggiA P)).mul (isPoly_w P)).add
    ((((IsPoly.const (ggA P)).mul (isPoly_xA P)).mul (isPoly_raising_constant P)).mul (isPoly_lowering_constant P))).add
    ((((IsPoly.const (ggA P)).mul (isPoly_raising_constant P)).mul (IsPoly.const (ggiA P))).mul (isPoly_S21 P))).add
    ((isPoly_S12 P).mul (isPoly_lowering_constant P))).add ((IsPoly.const (ggiA P)).mul (isPoly_quartic_sum P))
end Formalism.FourierDecayAlt.P.Mx7
