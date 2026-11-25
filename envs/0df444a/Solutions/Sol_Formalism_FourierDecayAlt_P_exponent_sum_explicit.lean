-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exponent_sum_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:33.263187+00:00
-- url     : https://prove2.me/submissions/2aa79b32-1c5e-4333-b3a3-700e3cd34530

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_D1_t_ExponentSumText

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
theorem _root_.solution : Formalism.FourierDecayAlt.PN.ExponentSumText := HermitianFormNormLemmas.D1.t_ExponentSumText
end Formalism.FourierDecayAlt.P
