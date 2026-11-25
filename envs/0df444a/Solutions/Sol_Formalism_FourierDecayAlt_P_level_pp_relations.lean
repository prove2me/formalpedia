-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_pp_relations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:20.247805+00:00
-- url     : https://prove2.me/submissions/c6622ca5-2f8c-4b0a-9335-9c36cb5729c1

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levPP

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
theorem _root_.solution : Formalism.FourierDecayAlt.M.LevPP := Mx2.levPP
end Formalism.FourierDecayAlt.P
