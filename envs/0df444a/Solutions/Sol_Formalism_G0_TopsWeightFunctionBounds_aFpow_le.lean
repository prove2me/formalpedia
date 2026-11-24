-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.aFpow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:23.170443+00:00
-- url     : https://prove2.me/submissions/2636c753-624a-47d6-a3f2-7a95a7ac3f71

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_aF_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_aF_le

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
theorem _root_.solution (h0 : 0 ≤ δ) (hLδ : (L₂ : ℝ) * δ ≤ 1) (k : ℕ) : aF L₂ δ ^ k ≤ 1 :=
  pow_le_one₀ (aF_nonneg hLδ) ((aF_le h0).trans (by norm_num))
end Formalism.G0.TopsWeightFunctionBounds
