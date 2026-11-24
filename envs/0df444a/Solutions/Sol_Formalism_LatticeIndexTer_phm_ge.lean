-- Prove2me | solution 1 for Formalism.LatticeIndexTer.phm_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:51:17.384003+00:00
-- url     : https://prove2.me/submissions/dc47dc7c-1128-48ba-94e4-8fad11a51110

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Theorems.Thm_Formalism_LatticeIndexTer_ph_ge_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Finset
namespace Formalism.LatticeIndexTer
theorem _root_.solution {x : ℝ} : -1 ≤ phm x := ph_ge_neg_one (le_trans zero_le_one (le_max_right x 1))
end Formalism.LatticeIndexTer
