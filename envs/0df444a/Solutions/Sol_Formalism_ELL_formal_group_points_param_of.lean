-- Prove2me | solution 1 for Formalism.ELL.formal_group_points_param_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:59.737051+00:00
-- url     : https://prove2.me/submissions/e9feea4c-018f-449f-a8e1-6f849669bf35

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Theorems.Thm_Formalism_ELL_formal_group_points_param_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
namespace Formalism.ELL
theorem _root_.solution (_hU : WSubstUnique.{u}) : FormalGroupPointsParametrisation.{u} := formal_group_points_param_holds
end Formalism.ELL
