-- Prove2me | solution 2 for CohnElkies.tendsto_saddleSmallResidueTruncation_div
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:29:21.944992+00:00
-- url     : https://prove2.me/submissions/1cd5cec9-9037-444e-84e6-e5667d3ae8bb

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
        (saddleSmallResidueTruncation ℓ : ℝ) / ℓ)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun ℓ : ℝ => Real.log ℓ / ℓ) atTop (𝓝 0) := by
    have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    simpa using this
  have hup : Tendsto (fun ℓ : ℝ => 20 * (Real.log ℓ / ℓ) + 2 * ℓ⁻¹) atTop (𝓝 0) := by
    simpa using (hlog.const_mul 20).add (tendsto_inv_atTop_zero.const_mul 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
    exact div_nonneg (Nat.cast_nonneg _) hℓ.le
  · filter_upwards [eventually_gt_atTop 1] with ℓ hℓ
    have hl : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ.le
    have hc : (saddleSmallResidueTruncation ℓ : ℝ) < 20 * Real.log ℓ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hne : ℓ ≠ 0 := (by linarith : (0:ℝ) < ℓ).ne'
    rw [div_le_iff₀ (by linarith)]
    have e : (20 * (Real.log ℓ / ℓ) + 2 * ℓ⁻¹) * ℓ = 20 * Real.log ℓ + 2 := by field_simp
    rw [e]; linarith

