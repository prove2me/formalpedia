-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.natCast_add_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:04.601467+00:00
-- url     : https://prove2.me/submissions/ba862ab7-8dff-4c2e-a0a1-6f0cbae98eb8

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
theorem _root_.solution (n : ℕ) : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by
  push_cast
  ring
end Formalism.FX.LFunctionPartialSum
