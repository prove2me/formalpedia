-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.wt_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:28.863199+00:00
-- url     : https://prove2.me/submissions/9942d469-f122-4b0a-b8a7-32aefceb6986

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_rpow_neg_three_halves
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_tele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.WeightedLatticeSum
open Finset
private theorem max_div_rpow_le_two_mul_inv_sqrt_sub (c K : ℝ) (hc : 0 < c) (hK : 2 ≤ K) (hcK : c ≤ K) :
    (max 1 (K / c)) ^ (-(3 / 2 : ℝ)) ≤
      2 * c * Real.sqrt c * (1 / Real.sqrt (K - 1) - 1 / Real.sqrt K) := by
  have hKpos : 0 < K := by linarith
  have hx : 1 ≤ K / c := by rw [le_div_iff₀ hc]; linarith
  rw [max_eq_right hx, rpow_neg_three_halves (lt_of_lt_of_le one_pos hx),
    Real.sqrt_div hKpos.le c]
  have ht := tele K hK
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have e : 1 / (K / c * (Real.sqrt K / Real.sqrt c)) = c * Real.sqrt c * (1 / (K * Real.sqrt K)) := by
    rw [div_mul_div_comm, one_div_div, mul_one_div]
  rw [e]
  calc c * Real.sqrt c * (1 / (K * Real.sqrt K))
      ≤ c * Real.sqrt c * (2 * (1 / Real.sqrt (K - 1) - 1 / Real.sqrt K)) :=
        mul_le_mul_of_nonneg_left ht (mul_pos hc hsc).le
    _ = 2 * c * Real.sqrt c * (1 / Real.sqrt (K - 1) - 1 / Real.sqrt K) := by ring
end Formalism.MainNotions.WeightedLatticeSum
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset
namespace Formalism.MainNotions.WeightedLatticeSum
theorem _root_.solution (R : ℝ) (hR : 1 ≤ R) (N : ℕ) (hN : 2 * R ≤ N) (j : ℕ) :
    wt R (N + 2 + j) ≤ 2 * (2 * R) * Real.sqrt (2 * R) *
      (1 / Real.sqrt ((N : ℝ) + (j : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((j + 1 : ℕ) : ℝ))) := by
  have hc : 0 < 2 * R := by linarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have e1 : ((N + 2 + j : ℕ) : ℝ) - 1 = (N : ℝ) + ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  have e2 : (N : ℝ) + (j : ℝ) = (N : ℝ) + ((j + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  have h := max_div_rpow_le_two_mul_inv_sqrt_sub (2 * R) ((N : ℝ) + ((j + 1 : ℕ) : ℝ)) hc (by push_cast; linarith)
    (by push_cast; linarith)
  unfold wt
  rw [e1, e2]
  exact h
end Formalism.MainNotions.WeightedLatticeSum
