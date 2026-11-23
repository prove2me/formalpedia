-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.phi_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:56.066287+00:00
-- url     : https://prove2.me/submissions/966cf7d8-db6f-438f-911c-732d7f7f3947

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.WeightedMeanData
noncomputable section
namespace Formalism.RankGapBounds.WeightedMeanData
theorem _root_.solution {u H X b U : ℝ} (hu : 0 ≤ u) (hH : 0 < H) (hHX : H ≤ X * b) (hb : 0 < b)
    (hX : 0 < X) (huU : u ≤ U) :
    u * Real.log (1 + H / u) ≤ Real.log (1 + X) * (U + b) := by
  have hL : 0 < Real.log (1 + X) := Real.log_pos (by linarith)
  have hX1 : 0 < 1 + X := by linarith
  rcases hu.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact mul_nonneg hL.le (by linarith)
  · have hw0 : 0 ≤ (1 + X)⁻¹ := inv_nonneg.mpr hX1.le
    have hw1 : (1 + X) * (1 + X)⁻¹ = 1 := mul_inv_cancel₀ hX1.ne'
    have hb0 : 1 - (1 + X)⁻¹ ≤ Real.log (1 + X) := by
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr hX1)
      rw [Real.log_inv] at this
      linarith
    have h1 : 0 < 1 + H / u := by
      have := div_nonneg hH.le hpos.le
      linarith
    have ha : Real.log (1 + H / u) ≤ Real.log (1 + X) + ((1 + H / u) * (1 + X)⁻¹ - 1) := by
      have := Real.log_le_sub_one_of_pos (mul_pos h1 (inv_pos.mpr hX1))
      rw [Real.log_mul h1.ne' (inv_pos.mpr hX1).ne', Real.log_inv] at this
      linarith
    have hyu : u * (H / u) = H := by
      rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, div_self hpos.ne', mul_one]
    have i1 := mul_le_mul_of_nonneg_left ha hu
    have e1 : u * (Real.log (1 + X) + ((1 + H / u) * (1 + X)⁻¹ - 1))
        = u * Real.log (1 + X) + u * (1 + X)⁻¹ + H * (1 + X)⁻¹ - u := by
      linear_combination (1 + X)⁻¹ * hyu
    have i2 := mul_le_mul_of_nonneg_right huU hL.le
    have hXw : X * (1 + X)⁻¹ = 1 - (1 + X)⁻¹ := by linear_combination hw1
    have hwle : (1 + X)⁻¹ ≤ 1 := by linarith [mul_nonneg hX.le hw0]
    have i3 : 0 ≤ u * (1 - (1 + X)⁻¹) := mul_nonneg hu (by linarith)
    have i4 : H * (1 + X)⁻¹ ≤ b * (1 - (1 + X)⁻¹) := by
      rw [← hXw]
      have := mul_le_mul_of_nonneg_right hHX hw0
      linarith
    have i5 := mul_le_mul_of_nonneg_left hb0 hb.le
    linarith
end Formalism.RankGapBounds.WeightedMeanData
