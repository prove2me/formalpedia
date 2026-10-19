-- Prove2me | solution 2 for CohnElkies.tendsto_saddleNegativeLogWindowTailMajorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:45.796368+00:00
-- url     : https://prove2.me/submissions/cd0eb996-0328-40f4-b3f8-28dc28586b69

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


theorem solution
    (C : ℝ) :
    Tendsto
      (fun ℓ : ℝ =>
        (1 + (Real.log ℓ / 8 + C)) *
          saddleSmallResidueTailMajorant C ℓ)
      atTop (𝓝 0) := by
  unfold saddleSmallResidueTailMajorant
  have hk : (0:ℝ) < 77 / 8 := by norm_num
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-(77 / 8 * t))) atTop (𝓝 0) := by
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hk)).const_mul (8 / 77)
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    simp only [Function.comp_apply, id, pow_one]
    ring
  have h2 : Tendsto (fun t : ℝ => Real.exp (-(77 / 8 * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hk))
  have h3 : Tendsto (fun t : ℝ => (1 + (t / 8 + C)) * Real.exp (3 * C - 77 / 8 * t)) atTop (𝓝 0) := by
    have := ((h2.const_mul (1 + C)).add (h1.const_mul (1 / 8))).const_mul (Real.exp (3 * C))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun t => ?_
    rw [show 3 * C - 77 / 8 * t = 3 * C + -(77 / 8 * t) by ring, Real.exp_add]
    ring
  exact h3.comp Real.tendsto_log_atTop

