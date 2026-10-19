-- Prove2me | solution 1 for CohnElkies.tendsto_saddleNegativeLogWindowTailMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/cb7eb692-786b-4ef8-9901-8a72594ecd5d

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
namespace CohnElkies
theorem _root_.solution
    (C : ℝ) :
    Tendsto
      (fun ℓ : ℝ =>
        (1 + (Real.log ℓ / 8 + C)) *
          saddleSmallResidueTailMajorant C ℓ)
      atTop (𝓝 0) := by
  have hscale :
      Tendsto
        (fun t : ℝ => (77 / 8 : ℝ) * t)
        atTop atTop :=
    tendsto_id.const_mul_atTop
      (by norm_num : (0 : ℝ) < 77 / 8)
  have h1base :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      hscale
  have h1 :
      Tendsto
        (fun t : ℝ =>
          t * Real.exp (-(77 / 8 : ℝ) * t))
        atTop (𝓝 0) := by
    convert! h1base.const_mul (8 / 77 : ℝ) using 1
    · funext t
      try dsimp
      ring_nf
    · norm_num
  have h0 :
      Tendsto
        (fun t : ℝ => Real.exp (-(77 / 8 : ℝ) * t))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using!
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg
          (by norm_num : (-(77 / 8 : ℝ)) < 0)))
  have hpoly :=
    (h1.const_mul (1 / 8 : ℝ)).add
      (h0.const_mul (1 + C))
  have hlog := hpoly.comp Real.tendsto_log_atTop
  have hscaled := hlog.const_mul (Real.exp (3 * C))
  convert! hscaled using 1
  · funext ℓ
    unfold saddleSmallResidueTailMajorant
    rw [show
      3 * C - (77 / 8 : ℝ) * Real.log ℓ =
        3 * C + (-(77 / 8 : ℝ)) * Real.log ℓ by ring,
      Real.exp_add]
    simp only [Function.comp_apply]
    ring
  · norm_num
end CohnElkies
