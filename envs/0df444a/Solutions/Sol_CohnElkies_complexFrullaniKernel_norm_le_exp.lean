-- Prove2me | solution 1 for CohnElkies.complexFrullaniKernel_norm_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/26c33873-6fcc-47b0-b8cf-67f4b4271edb

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_intervalIntegral_complexLaplaceSegment
import Theorems.Thm_CohnElkies_norm_complexLaplaceKernel
import Theorems.Thm_CohnElkies_complexFrullaniSegment_min_re_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (z w : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖complexFrullaniKernel z w x‖ ≤
      ‖w - z‖ *
        Real.exp (-(min z.re w.re) * x) := by
  rw [← intervalIntegral_complexLaplaceSegment z w hx.ne']
  have hbound :
      ‖∫ s in (0 : ℝ)..1,
          (w - z) *
            Complex.exp
              (-complexFrullaniSegment z w s * (x : ℂ))‖ ≤
        (‖w - z‖ *
          Real.exp (-(min z.re w.re) * x)) *
            |(1 : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hclosed : s ∈ Icc (0 : ℝ) 1 :=
      ⟨hs.1.le, hs.2⟩
    rw [norm_mul, norm_complexLaplaceKernel]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have hminimum :=
      complexFrullaniSegment_min_re_le z w hclosed
    nlinarith
  simpa using! hbound
end CohnElkies
