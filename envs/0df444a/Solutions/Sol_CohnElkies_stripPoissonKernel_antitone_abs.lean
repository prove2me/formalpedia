-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_antitone_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/e2f011bc-871a-4ad6-ad62-2ba2c4abb150

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripAngle_mem_Ioo

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {x y : ℝ} (hxy : |x| ≤ |y|) :
    stripPoissonKernel σ y ≤ stripPoissonKernel σ x := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hcos : Real.cos (stripAngle σ) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ)
      (by norm_num) hangle'.le hangle
    simpa using! h
  have hxden :
      0 < 4 *
        (Real.cosh (Real.pi * x / 2) -
          Real.cos (stripAngle σ)) := by
    have hxcosh := Real.one_le_cosh (Real.pi * x / 2)
    nlinarith
  have hcosh :
      Real.cosh (Real.pi * x / 2) ≤
        Real.cosh (Real.pi * y / 2) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_div, abs_div, abs_mul, abs_mul]
    gcongr
  have hden :
      4 * (Real.cosh (Real.pi * x / 2) -
          Real.cos (stripAngle σ)) ≤
        4 * (Real.cosh (Real.pi * y / 2) -
          Real.cos (stripAngle σ)) := by
    linarith
  unfold stripPoissonKernel
  exact div_le_div_of_nonneg_left hsin.le hxden hden
end CohnElkies
