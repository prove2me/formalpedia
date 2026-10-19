-- Prove2me | solution 2 for CohnElkies.tendsto_saddleNegativeTruncation_odd_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:17:15.21487+00:00
-- url     : https://prove2.me/submissions/27e0dec1-fda6-428c-b39b-3f70003cbb9b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators


theorem solution :
    Tendsto
      (fun ℓ : ℝ =>
        (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 / ℓ)
      atTop (𝓝 0) := by
  have hpow : ∀ n : ℕ, Tendsto (fun x : ℝ => Real.log x ^ n / x) atTop (𝓝 0) := by
    intro n
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
    simpa using this
  have hg : Tendsto (fun ℓ : ℝ => 1600 * (Real.log ℓ ^ 2 / ℓ) + 240 * (Real.log ℓ ^ 1 / ℓ) +
      9 * (Real.log ℓ ^ 0 / ℓ)) atTop (𝓝 0) := by
    have := (((hpow 2).const_mul 1600).add ((hpow 1).const_mul 240)).add ((hpow 0).const_mul 9)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with ℓ hℓ
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with ℓ hℓ
    have hL : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
    have hN : (saddleSmallResidueTruncation ℓ : ℝ) < 20 * Real.log ℓ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hN0 : (0:ℝ) ≤ (saddleSmallResidueTruncation ℓ : ℝ) := Nat.cast_nonneg _
    have hℓ0 : 0 < ℓ := by linarith
    have hsq : (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 ≤ (40 * Real.log ℓ + 3) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    calc (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 / ℓ ≤ (40 * Real.log ℓ + 3) ^ 2 / ℓ :=
          div_le_div_of_nonneg_right hsq hℓ0.le
      _ = _ := by field_simp; ring

