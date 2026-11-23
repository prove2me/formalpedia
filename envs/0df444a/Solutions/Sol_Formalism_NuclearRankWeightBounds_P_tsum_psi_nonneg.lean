-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.tsum_psi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:08.435798+00:00
-- url     : https://prove2.me/submissions/bec22b09-2ebe-41a8-92e5-18dfb6f72265

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_psi_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : 0 ≤ ∑' n, psi n := tsum_nonneg psi_nonneg
end Formalism.NuclearRankWeightBounds.P
