-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.inv_iter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:47.016804+00:00
-- url     : https://prove2.me/submissions/3fd44d63-7b87-4c51-ab13-a605b4723fa6

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_runS_cons
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_inv_step
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Ls_succ

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
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution {n : ℕ} (hn : Even n) {T : Finset ℕ} {L₂ R b K₀ : ℕ} (hR : 1 ≤ R) (m : ℕ) :
    ∀ t s, Inv n T L₂ R b K₀ t s → Inv n T L₂ R b K₀ (t + m) (runS R L₂ s (Ls n T b t m)) := by
  induction m with
  | zero => intro t s hs; simpa [Ls, runS] using hs
  | succ m ih =>
    intro t s hs
    rw [Ls_succ, runS_cons]
    have := ih (t + 1) _ (inv_step hn hR t s hs)
    rwa [show t + 1 + m = t + (m + 1) by omega] at this
end Formalism.G0.TopsWeightFunctionBounds
