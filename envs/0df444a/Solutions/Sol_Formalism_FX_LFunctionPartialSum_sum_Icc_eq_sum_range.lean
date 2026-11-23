-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.sum_Icc_eq_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:18.796113+00:00
-- url     : https://prove2.me/submissions/27cca75c-294b-4b5f-a80f-b10aeaa85f12

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
theorem _root_.solution (f : ℕ → ℂ) (hf : f 0 = 0) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, f n = ∑ n ∈ Finset.range (M + 1), f n := by
  induction M with
  | zero => simp [hf]
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    exact (Finset.sum_range_succ f (M + 1)).symm
end Formalism.FX.LFunctionPartialSum
