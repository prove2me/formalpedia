-- Prove2me | solution 1 for CohnElkies.complexFrullaniShiftKernel_norm_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/acab3d3f-3f7b-41c1-a9a7-b8d10250e3e6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniKernel_norm_le_exp

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
    (z : ℂ) {s x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 < x) :
    ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖ ≤
      (‖(1 : ℂ) - z‖ + 1) *
        Real.exp (-(min z.re 1) * x) := by
  have hnorm :
      ‖(1 : ℂ) - (z + (s : ℂ))‖ ≤
        ‖(1 : ℂ) - z‖ + 1 := by
    calc
      ‖(1 : ℂ) - (z + (s : ℂ))‖ =
          ‖((1 : ℂ) - z) - (s : ℂ)‖ := by
            congr 1
            ring
      _ ≤ ‖(1 : ℂ) - z‖ + ‖(s : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ ‖(1 : ℂ) - z‖ + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs.1]
        linarith [hs.2]
  have hmin :
      min z.re 1 ≤
        min (z + (s : ℂ)).re (1 : ℂ).re := by
    apply le_min
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith [min_le_left z.re (1 : ℝ), hs.1]
    · exact min_le_right z.re (1 : ℝ)
  calc
    ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖ ≤
      ‖(1 : ℂ) - (z + (s : ℂ))‖ *
        Real.exp
          (-(min (z + (s : ℂ)).re (1 : ℂ).re) * x) :=
      complexFrullaniKernel_norm_le_exp (z + (s : ℂ)) 1 hx
    _ ≤ (‖(1 : ℂ) - z‖ + 1) *
        Real.exp
          (-(min (z + (s : ℂ)).re (1 : ℂ).re) * x) :=
      mul_le_mul_of_nonneg_right hnorm (Real.exp_pos _).le
    _ ≤ (‖(1 : ℂ) - z‖ + 1) *
        Real.exp (-(min z.re 1) * x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith
end CohnElkies
