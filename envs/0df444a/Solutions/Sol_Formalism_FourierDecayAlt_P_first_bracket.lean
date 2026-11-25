-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.first_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:16.222885+00:00
-- url     : https://prove2.me/submissions/86172f01-749c-44eb-b57b-93d439d28617

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_D1_t_FirstBracket

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.PN.FirstBracket := HermitianFormNormLemmas.D1.t_FirstBracket
end Formalism.FourierDecayAlt.P
