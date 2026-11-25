-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.zeta_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:00:57.333831+00:00
-- url     : https://prove2.me/submissions/d2b53b5e-98e9-4733-b336-f9bd51598094

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_zetaTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.ZetaTail := Sz2.zetaTail
end Formalism.FourierDecayAlt.P
