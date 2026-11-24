-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.WF_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:23.617968+00:00
-- url     : https://prove2.me/submissions/2f6578db-1f5d-467a-a2ab-43d574cf4c89

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB

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
theorem _root_.solution (hR : 1 ≤ R) (s : St) (hs : WF R s) (b : Bool) : WF R (step R L₂ s b) := by
  cases s with
  | bad => cases b <;> trivial
  | good => cases b <;> trivial
  | run K j d al ev =>
    simp only [WF] at hs
    cases b
    · simpa [step, WF] using hs
    · simp only [step]
      split_ifs with h1 h2 h3
      · trivial
      · trivial
      · simp only [WF]; omega
      · simp only [WF]; omega
end Formalism.G0.TopsWeightFunctionBounds
