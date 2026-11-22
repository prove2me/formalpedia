-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.dterm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:06.128801+00:00
-- url     : https://prove2.me/submissions/4a2e3aeb-40e0-49f8-9291-b14b5f26eea1

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_Ap_zero

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
theorem _root_.solution (s : ℂ) : dterm χ s 0 = 0 := by
  simp [dterm, Ap_zero]
end Formalism.FX.LFunctionPartialSum
