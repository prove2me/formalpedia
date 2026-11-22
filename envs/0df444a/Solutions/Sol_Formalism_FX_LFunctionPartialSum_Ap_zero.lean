-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.Ap_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:13.560624+00:00
-- url     : https://prove2.me/submissions/fef55558-b52b-4cf7-b0cf-0049d314b210

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt

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
theorem _root_.solution : Ap χ 0 = 0 := by
  simp [Ap]
end Formalism.FX.LFunctionPartialSum
