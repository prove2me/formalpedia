-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_p_relations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:09.488161+00:00
-- url     : https://prove2.me/submissions/5bb0069e-bbe7-4151-a0dc-9641b43c0f63

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.LevP := Mx2.levP
end Formalism.FourierDecayAlt.P
