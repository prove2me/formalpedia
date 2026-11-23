-- Prove2me | solution 1 for Formalism.FX.succ_le_max_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:41.788862+00:00
-- url     : https://prove2.me/submissions/f2cb3372-4d95-4679-9966-cf8589a97535

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_DivisorBound
import Theorems.Thm_Formalism_FX_succ_le_max_mul_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FX
open Finset
namespace Formalism.FX
theorem _root_.solution (e : ℝ) (he : 0 < e) (p k : ℕ) (hp : 2 ≤ p) :
    ((k : ℝ) + 1) ≤ max 1 (1 / (e * Real.log 2)) * ((p : ℝ) ^ e) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  have ha : 0 < e * Real.log 2 := mul_pos he (Real.log_pos (by norm_num))
  refine (succ_le_max_mul_exp _ ha k).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (le_max_left _ _))
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc e * Real.log 2 * k ≤ e * Real.log p * k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog he.le) hk
    _ = k * (Real.log p * e) := by ring
end Formalism.FX
