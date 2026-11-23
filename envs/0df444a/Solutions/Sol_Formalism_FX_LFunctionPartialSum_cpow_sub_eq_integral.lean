-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.cpow_sub_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:53.319429+00:00
-- url     : https://prove2.me/submissions/efe4f0af-8869-4d80-8f02-4d5ed4ec320e

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
theorem _root_.solution {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    (x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s) = s * ∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1) := by
  have hderiv : ∀ t ∈ Set.uIcc x (x + 1),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t := fun t ht =>
    (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (pos_of_mem_uIcc_self_add_one hx ht))).hasDerivAt.comp_ofReal
  have hint : IntervalIntegrable (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) MeasureTheory.volume x (x + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hc : ContinuousAt (fun z : ℂ => z ^ (-s - 1)) (t : ℂ) :=
      (Complex.hasStrictDerivAt_cpow_const (c := -s - 1)
        (Complex.ofReal_mem_slitPlane.mpr (pos_of_mem_uIcc_self_add_one hx ht))).hasDerivAt.continuousAt
    exact (continuousAt_const.mul (hc.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at h
  have e : s * ∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1) =
      -(-s * ∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1)) := by ring
  rw [e, h]
  ring
end Formalism.FX.LFunctionPartialSum
