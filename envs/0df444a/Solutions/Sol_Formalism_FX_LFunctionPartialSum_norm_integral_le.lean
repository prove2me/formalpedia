-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.norm_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:13.038073+00:00
-- url     : https://prove2.me/submissions/c121533e-d8a1-4e77-9d22-20f0a68d4aa2

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
theorem _root_.solution {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1)‖ ≤ ∫ t in x..(x + 1), t ^ (-s.re - 1) := by
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := lt_trans hx ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    apply le_of_eq
    simp
  · exact (continuousOn_id.rpow_const fun t ht => Or.inl (pos_of_mem_uIcc_self_add_one hx ht).ne').intervalIntegrable
end Formalism.FX.LFunctionPartialSum
