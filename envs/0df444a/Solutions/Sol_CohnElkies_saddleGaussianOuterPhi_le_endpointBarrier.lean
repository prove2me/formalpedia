-- Prove2me | solution 1 for CohnElkies.saddleGaussianOuterPhi_le_endpointBarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/3c9cb5b7-1181-4cd5-b7e8-358091376182

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
namespace CohnElkies
theorem _root_.solution
    {B Q c ℓ δ₀ δ : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hc : 0 < c)
    (hℓ : 0 ≤ ℓ) (hδ₀ : 0 ≤ δ₀) (hδ : δ₀ ≤ δ)
    (hscale :
      (B + 1) / 2 + 4 ≤
        c * ℓ * Q * B * Real.exp (B * δ₀)) :
    saddleGaussianOuterPhi B Q c ℓ δ ≤
      ((B + 1) / 2 + 4) * δ₀ + 4 -
        c * ℓ * Q * Real.exp (B * δ₀) := by
  have hδnonneg : 0 ≤ δ := hδ₀.trans hδ
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < 2 + δ by linarith)
  have hexpstep :
      Real.exp (B * δ₀) *
          (1 + B * (δ - δ₀)) ≤
        Real.exp (B * δ) := by
    calc
      Real.exp (B * δ₀) *
          (1 + B * (δ - δ₀)) ≤
        Real.exp (B * δ₀) *
          Real.exp (B * (δ - δ₀)) := by
            gcongr
            simpa [add_comm] using!
              Real.add_one_le_exp (B * (δ - δ₀))
      _ = Real.exp (B * δ) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hdifference :
      Real.exp (B * δ₀) * (B * (δ - δ₀)) ≤
        Real.exp (B * δ) - Real.exp (B * δ₀) := by
    nlinarith
  have hcoefficient : 0 ≤ c * ℓ * Q := by
    apply (mul_nonneg_iff_of_pos_right hB).mp
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hc.le hℓ) hQ.le) hB.le
  have hexpscaled :=
    mul_le_mul_of_nonneg_left hdifference hcoefficient
  have hlinearscaled :=
    mul_le_mul_of_nonneg_right hscale
      (show 0 ≤ δ - δ₀ by linarith)
  unfold saddleGaussianOuterPhi
  nlinarith
end CohnElkies
