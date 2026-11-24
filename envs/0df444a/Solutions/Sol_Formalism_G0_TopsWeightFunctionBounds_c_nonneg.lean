-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.c_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:50.564043+00:00
-- url     : https://prove2.me/submissions/5f3655c7-8581-4f82-b7ad-6369e4beb64a

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_aFpow_le

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
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (h0 : 0 ≤ δ) (hLδ : (L₂ : ℝ) * δ ≤ 1) : 0 ≤ 1 - aF L₂ δ ^ R := by
  linarith [aFpow_le h0 hLδ R]
end Formalism.G0.TopsWeightFunctionBounds
