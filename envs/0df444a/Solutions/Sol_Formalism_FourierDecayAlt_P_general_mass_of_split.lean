-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.general_mass_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:17.242285+00:00
-- url     : https://prove2.me/submissions/94f6e3ac-06f0-4497-9205-1e22de69e0d9

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_E_t_GenMassOfSplit

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
theorem _root_.solution : Formalism.FourierDecayAlt.PN.GenMassOfSplit := HermitianFormNormLemmas.E.t_GenMassOfSplit
end Formalism.FourierDecayAlt.P
