-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.Ap_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:17.201801+00:00
-- url     : https://prove2.me/submissions/e6de85eb-e25d-4976-bc37-60c4ac11a367

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
theorem _root_.solution (n : ℕ) : Ap χ (n + 1) = Ap χ n + χ ((n + 1 : ℕ) : ZMod q) := by
  simp only [Ap]
  rw [Finset.sum_Icc_succ_top (by omega)]
end Formalism.FX.LFunctionPartialSum
