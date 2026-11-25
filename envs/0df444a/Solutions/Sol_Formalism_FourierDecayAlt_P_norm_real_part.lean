-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.norm_real_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:44:24.223029+00:00
-- url     : https://prove2.me/submissions/0920c20a-b768-4ec0-8678-145640614c3a

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_A_t_NormRe

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
theorem _root_.solution : Formalism.FourierDecayAlt.PN.NormRe := HermitianFormNormLemmas.A.t_NormRe
end Formalism.FourierDecayAlt.P
