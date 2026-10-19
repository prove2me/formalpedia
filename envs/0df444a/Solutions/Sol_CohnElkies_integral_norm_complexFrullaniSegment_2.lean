-- Prove2me | solution 2 for CohnElkies.integral_norm_complexFrullaniSegment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:43.494433+00:00
-- url     : https://prove2.me/submissions/9784fa21-060f-417f-97d3-ec113b5fd33a

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


theorem solution
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ x : ℝ in Ioi 0,
      ‖(w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))‖) =
      ‖w - z‖ * (complexFrullaniSegment z w s).re⁻¹ := by
  have hre : 0 < (complexFrullaniSegment z w s).re := by
    unfold complexFrullaniSegment
    simp
    have hm : 0 < min z.re w.re := lt_min hz hw
    have h1 : (1 - s) * min z.re w.re ≤ (1 - s) * z.re :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith [hs.2])
    have h2 : s * min z.re w.re ≤ s * w.re := mul_le_mul_of_nonneg_left (min_le_right _ _) hs.1
    nlinarith
  have hfun : ∀ x : ℝ, ‖(w - z) * Complex.exp (-complexFrullaniSegment z w s * (x : ℂ))‖ =
      ‖w - z‖ * Real.exp (-(complexFrullaniSegment z w s).re * x) := by
    intro x
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  simp_rw [hfun]
  rw [integral_const_mul, integral_laplaceKernel hre]

