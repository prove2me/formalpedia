-- Prove2me | solution 1 for Formalism.FX.l_function_partial_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:03.107497+00:00
-- url     : https://prove2.me/submissions/94772d67-433b-48eb-959f-3f7af90dea85

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_tail_le
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_LFunction_eq_G
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_natCast_add_one_eq
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_partial_identity
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_summable_dterm


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
open LFunctionPartialSum
namespace Formalism.FX
theorem _root_.solution : LPartialSum := by
  intro q _ χ hχ B hB s hs N hN
  have hB' : ∀ M, ‖Ap χ M‖ ≤ B := hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  rw [LFunction_eq_G χ hχ hB' hs, ← partial_identity χ s N]
  have hsum := summable_dterm χ hB' hs
  have hG : LFunctionPartialSum.G χ s = ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) :=
    (hsum.sum_add_tsum_nat_add (N + 1)).symm
  rw [hG]
  have e : ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) -
      (∑ n ∈ Finset.range (N + 1), dterm χ s n + Ap χ N * ((N : ℂ) + 1) ^ (-s)) =
      ∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s) := by ring
  rw [e]
  have h1 := norm_tail_le χ hB' hs N
  have h2 : ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ ≤ B * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB' N) (Real.rpow_nonneg (by positivity) _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : ((N : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hNpos (by linarith) (by linarith)
  have hq : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have h4 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  have h5 : 0 ≤ ((N : ℝ) + 1) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  calc ‖∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑' i, dterm χ s (i + (N + 1))‖ + ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) + B * ((N : ℝ) + 1) ^ (-s.re) := add_le_add h1 h2
    _ = B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by ring
    _ ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hB0 (by linarith))
    _ ≤ 2 * B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have : 0 ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
          mul_nonneg (mul_nonneg hB0 (by linarith)) h4
        linarith
end Formalism.FX
