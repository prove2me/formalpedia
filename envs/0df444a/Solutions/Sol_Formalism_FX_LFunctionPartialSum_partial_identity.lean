-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.partial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:16.350802+00:00
-- url     : https://prove2.me/submissions/1eef04a0-9f11-45f4-b495-afd63d9a27ee

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_Ap_zero
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_Ap_succ
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_dterm_zero

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
theorem _root_.solution (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), dterm χ s n + Ap χ M * ((M : ℂ) + 1) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q) * (n : ℂ) ^ (-s) := by
  induction M with
  | zero => simp [dterm_zero, Ap_zero]
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ← ih]
    simp only [dterm]
    rw [Ap_succ]
    push_cast
    ring
end Formalism.FX.LFunctionPartialSum
