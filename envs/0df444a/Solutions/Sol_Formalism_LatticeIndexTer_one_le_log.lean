-- Prove2me | solution 1 for Formalism.LatticeIndexTer.one_le_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:33.069674+00:00
-- url     : https://prove2.me/submissions/a825c54d-98cd-41f6-9ca8-866ea6976f2b

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails

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
theorem _root_.solution {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
end Formalism.LatticeIndexTer
