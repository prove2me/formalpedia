-- Prove2me | solution 1 for AvramDividend.Classical.neg_jump_exp_deficit_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:13:31.399984+00:00
-- url     : https://prove2.me/submissions/b04f4079-43ba-4025-87c6-d78a8a6c1a53

import Mathlib

open Filter

theorem solution (y : ℝ) (hy : y ≤ 0) :
    Tendsto (fun θ : ℝ => (1 - Real.exp (θ * y)) / θ)
      atTop (nhds (0 : ℝ)) := by
  have hbounds :
      ∀ᶠ θ : ℝ in atTop,
        0 ≤ (1 - Real.exp (θ * y)) / θ ∧
          (1 - Real.exp (θ * y)) / θ ≤ θ⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
    have hty : θ * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ.le hy
    have he : Real.exp (θ * y) ≤ 1 := by
      have h := (Real.exp_le_exp).2 hty
      simpa only [Real.exp_zero] using h
    constructor
    · exact div_nonneg (sub_nonneg.mpr he) hθ.le
    · apply (div_le_iff₀ hθ).2
      have hc : θ⁻¹ * θ = 1 :=
        inv_mul_cancel₀ (ne_of_gt hθ)
      rw [hc]
      linarith [Real.exp_pos (θ * y)]
  exact squeeze_zero'
    (hbounds.mono (fun θ h => h.1))
    (hbounds.mono (fun θ h => h.2))
    (tendsto_inv_atTop_zero : Tendsto (fun θ : ℝ => θ⁻¹) atTop (nhds 0))
