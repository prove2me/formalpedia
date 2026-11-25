-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.chain_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:36:42.542873+00:00
-- url     : https://prove2.me/submissions/3881fa91-57fe-43f6-90da-b02ee61c2432

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_chainSum_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.ChainSum := Formalism.FourierDecayAlt.P.ChainAndRowSums.chainSum_ok
end Formalism.FourierDecayAlt.P
