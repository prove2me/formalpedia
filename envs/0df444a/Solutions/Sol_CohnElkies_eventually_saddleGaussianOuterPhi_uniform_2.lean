-- Prove2me | solution 2 for CohnElkies.eventually_saddleGaussianOuterPhi_uniform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:36:51.827989+00:00
-- url     : https://prove2.me/submissions/33dc9246-4deb-4299-aa7d-a1a826651081

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology


theorem solution
    {B Q c δ₀ : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hc : 0 < c)
    (hδ₀ : 0 ≤ δ₀) :
    ∀ κ : ℝ, 0 < κ →
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, δ₀ ≤ δ →
          Real.sqrt ℓ *
              Real.exp (saddleGaussianOuterPhi B Q c ℓ δ) < κ := by
  intro κ hκ
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (B + 1) / (2 * B) + 4 * (1 + 1 / B) := ⟨_, rfl⟩
  have ha : 0 < c * Q := mul_pos hc hQ
  have hlim : Tendsto (fun ℓ : ℝ => Real.exp M * (ℓ ^ (1 / 2 : ℝ) * Real.exp (-(c * Q) * ℓ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (c * Q) ha).const_mul
      (Real.exp M)
  filter_upwards [hlim.eventually (gt_mem_nhds hκ), eventually_ge_atTop (M / (c * Q)),
    eventually_ge_atTop (0 : ℝ)] with ℓ h1 h2 h3 δ hδ
  have hδ0 : 0 ≤ δ := le_trans hδ₀ hδ
  have hE : 1 ≤ Real.exp (B * δ) := Real.one_le_exp (by positivity)
  have hbound : (B + 1) / 2 * δ + 4 * Real.log (2 + δ) ≤ M * Real.exp (B * δ) := by
    have e1 : B * δ + 1 ≤ Real.exp (B * δ) := Real.add_one_le_exp (B * δ)
    have hd : δ ≤ Real.exp (B * δ) / B := by rw [le_div_iff₀ hB]; linarith
    have hl : Real.log (2 + δ) ≤ 1 + δ := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 2 + δ); linarith
    have hM : M * Real.exp (B * δ) =
        (B + 1) / 2 * (Real.exp (B * δ) / B) + 4 * (Real.exp (B * δ) + Real.exp (B * δ) / B) := by
      rw [hMdef]; field_simp <;> ring
    rw [hM]
    have hB1 : 0 ≤ (B + 1) / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hd hB1]
  have hcQ : M ≤ c * Q * ℓ := by
    rw [div_le_iff₀ ha] at h2; linarith
  have hφ : saddleGaussianOuterPhi B Q c ℓ δ ≤ M - c * Q * ℓ := by
    unfold saddleGaussianOuterPhi
    have := mul_le_mul_of_nonpos_left hE (by linarith : M - c * Q * ℓ ≤ 0)
    nlinarith
  calc Real.sqrt ℓ * Real.exp (saddleGaussianOuterPhi B Q c ℓ δ)
      ≤ Real.sqrt ℓ * Real.exp (M - c * Q * ℓ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hφ) (Real.sqrt_nonneg _)
    _ = Real.exp M * (ℓ ^ (1 / 2 : ℝ) * Real.exp (-(c * Q) * ℓ)) := by
        rw [Real.sqrt_eq_rpow, show -(c * Q) * ℓ = -(c * Q * ℓ) by ring, sub_eq_add_neg, Real.exp_add]
        ring
    _ < κ := h1

