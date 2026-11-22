-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.lo_le_hi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:35:59.663803+00:00
-- url     : https://prove2.me/submissions/7de419ca-cc47-438d-9783-aaff990cd3d7

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_two_sub_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : (1 - δ) / (2 - δ) ≤ 1 / (2 - δ) := by
  have h2 := two_sub_pos h1
  exact div_le_div_of_nonneg_right (by linarith) h2.le
end Formalism.G0.TopsWeightFunctionBounds
