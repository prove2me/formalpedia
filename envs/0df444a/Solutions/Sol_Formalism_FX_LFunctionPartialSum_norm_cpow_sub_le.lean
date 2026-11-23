-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.norm_cpow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:43.530405+00:00
-- url     : https://prove2.me/submissions/a77405fb-8aab-4fba-b4c2-77b88e849012

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_cpow_sub_eq_integral
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_integral_le
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_integral_rpow_eq

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
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖s‖ / s.re * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  rw [cpow_sub_eq_integral hx hs0, norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_integral_le hx s) (norm_nonneg _)) (le_of_eq ?_)
  rw [integral_rpow_eq hx hs]
  ring
end Formalism.FX.LFunctionPartialSum
