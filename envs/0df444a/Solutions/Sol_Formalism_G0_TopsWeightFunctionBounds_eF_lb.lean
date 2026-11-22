-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.eF_lb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:00.103219+00:00
-- url     : https://prove2.me/submissions/8009fcef-14c1-4cbb-b4e9-26ab823558a5

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_lo_le_hi

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
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (d : ℕ) : (1 - δ) / (2 - δ) ≤ eF δ d := by
  unfold eF; split_ifs
  · exact le_rfl
  · exact lo_le_hi h0 h1
end Formalism.G0.TopsWeightFunctionBounds
