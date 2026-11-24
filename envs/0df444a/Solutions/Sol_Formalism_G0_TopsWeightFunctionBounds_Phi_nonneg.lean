-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.Phi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:58.86806+00:00
-- url     : https://prove2.me/submissions/122e84f7-4ff2-407d-94c2-9473e2a6b798

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_c_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_GF_le_one

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
theorem _root_.solution (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (s : St) :
    0 ≤ Phi R L₂ δ s := by
  cases s with
  | bad => simp [Phi]
  | good => simp [Phi]
  | run K j d al ev =>
    simp only [Phi]
    exact mul_nonneg (pow_nonneg (c_nonneg h0 hLδ) _) (by linarith [GF_le_one (R := R) h0 hL hLδ j d al ev])
end Formalism.G0.TopsWeightFunctionBounds
