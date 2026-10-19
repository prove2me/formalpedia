-- Prove2me | solution 1 for CohnElkies.integral_norm_complexFrullaniSegment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/0395f368-7818-4c8c-a5c0-cc992344b5b9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniSegment_re_pos
import Theorems.Thm_CohnElkies_norm_complexLaplaceKernel

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
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ x : ℝ in Ioi 0,
      ‖(w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))‖) =
      ‖w - z‖ * (complexFrullaniSegment z w s).re⁻¹ := by
  have hpositive := complexFrullaniSegment_re_pos hz hw hs
  calc
    (∫ x : ℝ in Ioi 0,
      ‖(w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))‖) =
      ∫ x : ℝ in Ioi 0,
        ‖w - z‖ *
          Real.exp (-(complexFrullaniSegment z w s).re * x) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            change
              ‖(w - z) *
                  Complex.exp
                    (-complexFrullaniSegment z w s * (x : ℂ))‖ =
                ‖w - z‖ *
                  Real.exp
                    (-(complexFrullaniSegment z w s).re * x)
            rw [norm_mul, norm_complexLaplaceKernel]
    _ = ‖w - z‖ *
        (∫ x : ℝ in Ioi 0,
          Real.exp (-(complexFrullaniSegment z w s).re * x)) := by
            rw [integral_const_mul]
    _ = ‖w - z‖ * (complexFrullaniSegment z w s).re⁻¹ := by
      rw [integral_laplaceKernel hpositive]
end CohnElkies
