-- Prove2me | solution 2 for CohnElkies.tendsto_saddleSmallResidueTruncation_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:00.853843+00:00
-- url     : https://prove2.me/submissions/6588f16c-e0fa-43a3-9a7a-1408225a078b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution :
    Tendsto
      (fun ℓ : ℝ =>
        (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ)
      atTop (𝓝 0) := by
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hup : Tendsto (fun ℓ : ℝ => 400 * (Real.log ℓ ^ 2 / ℓ) + 40 * (Real.log ℓ / ℓ) + ℓ⁻¹)
      atTop (𝓝 0) := by
    have := ((h2.const_mul 400).add (h1.const_mul 40)).add tendsto_inv_atTop_zero
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [eventually_gt_atTop 0] with ℓ h
    positivity
  · filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
    have hL := Real.log_nonneg hℓ
    have hN : (saddleSmallResidueTruncation ℓ : ℝ) ≤ 20 * Real.log ℓ + 1 := by
      unfold saddleSmallResidueTruncation
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hN0 : (0 : ℝ) ≤ saddleSmallResidueTruncation ℓ := Nat.cast_nonneg _
    have hsq : (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 ≤
        400 * Real.log ℓ ^ 2 + 40 * Real.log ℓ + 1 := by nlinarith
    calc (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ
        ≤ (400 * Real.log ℓ ^ 2 + 40 * Real.log ℓ + 1) / ℓ :=
          div_le_div_of_nonneg_right hsq (by linarith)
      _ = 400 * (Real.log ℓ ^ 2 / ℓ) + 40 * (Real.log ℓ / ℓ) + ℓ⁻¹ := by ring

