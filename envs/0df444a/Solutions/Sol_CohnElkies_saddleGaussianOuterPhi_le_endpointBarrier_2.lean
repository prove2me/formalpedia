-- Prove2me | solution 2 for CohnElkies.saddleGaussianOuterPhi_le_endpointBarrier
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:28:13.856744+00:00
-- url     : https://prove2.me/submissions/30393052-3415-4246-8051-cc18ac85409d

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
    {B Q c ℓ δ₀ δ : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hc : 0 < c)
    (hℓ : 0 ≤ ℓ) (hδ₀ : 0 ≤ δ₀) (hδ : δ₀ ≤ δ)
    (hscale :
      (B + 1) / 2 + 4 ≤
        c * ℓ * Q * B * Real.exp (B * δ₀)) :
    saddleGaussianOuterPhi B Q c ℓ δ ≤
      ((B + 1) / 2 + 4) * δ₀ + 4 -
        c * ℓ * Q * Real.exp (B * δ₀) := by
  unfold saddleGaussianOuterPhi
  have hlog : Real.log (2 + δ) ≤ 1 + δ := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 + δ by linarith); linarith
  have hE0 := Real.exp_pos (B * δ₀)
  have he : Real.exp (B * δ₀) * (1 + B * (δ - δ₀)) ≤ Real.exp (B * δ) := by
    rw [show B * δ = B * δ₀ + B * (δ - δ₀) by ring, Real.exp_add]
    have := Real.add_one_le_exp (B * (δ - δ₀))
    nlinarith
  have hK : 0 ≤ c * ℓ * Q := by positivity
  have h2 := mul_le_mul_of_nonneg_right hscale (sub_nonneg.2 hδ)
  have h3 := mul_le_mul_of_nonneg_left he hK
  nlinarith

