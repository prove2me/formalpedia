-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.integral_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:47.71185+00:00
-- url     : https://prove2.me/submissions/421950b7-8548-4bdf-99e7-509268dfa6fe

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
    ∫ t in x..(x + 1), t ^ (-σ - 1) ≤ x ^ (-σ - 1) := by
  have h1 : ∫ t in x..(x + 1), t ^ (-σ - 1) ≤ ∫ t in x..(x + 1), x ^ (-σ - 1) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuousOn_id.rpow_const fun t ht => Or.inl (pos_of_mem_uIcc_self_add_one hx ht).ne').intervalIntegrable
    · exact intervalIntegrable_const
    · intro t ht
      exact Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)
  simpa using h1
end Formalism.FX.LFunctionPartialSum
