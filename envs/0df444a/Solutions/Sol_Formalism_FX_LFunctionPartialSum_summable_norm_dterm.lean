-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.summable_norm_dterm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:52.181727+00:00
-- url     : https://prove2.me/submissions/9e78b5a3-0658-4797-8584-b9ebd0306eaf

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_dterm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n => ‖dterm χ s n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_dterm_le χ hB hs) ?_
  exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left ‖s‖).mul_left B
end Formalism.FX.LFunctionPartialSum
