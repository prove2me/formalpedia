-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.integral_rpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:05.353143+00:00
-- url     : https://prove2.me/submissions/760b2699-a01c-47a8-a789-56b9d266671d

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Filter Topology
noncomputable section
namespace Formalism.FX
namespace LFunctionPartialSum
private lemma pos_of_mem_uIcc_self_add_one {x t : ℝ} (hx : 0 < x) (ht : t ∈ Set.uIcc x (x + 1)) : 0 < t := by
  rw [Set.uIcc_of_le (by linarith)] at ht
  exact lt_of_lt_of_le hx ht.1
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
end LFunctionPartialSum
end Formalism.FX
end
end

set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in x..(x + 1), t ^ (-σ - 1) = (x ^ (-σ) - (x + 1) ^ (-σ)) / σ := by
  rw [integral_rpow (Or.inr ⟨by linarith, fun h0 => lt_irrefl 0 (pos_of_mem_uIcc_self_add_one hx h0)⟩)]
  have e : -σ - 1 + 1 = -σ := by ring
  rw [e, div_neg, ← neg_div, neg_sub]
end Formalism.FX.LFunctionPartialSum
