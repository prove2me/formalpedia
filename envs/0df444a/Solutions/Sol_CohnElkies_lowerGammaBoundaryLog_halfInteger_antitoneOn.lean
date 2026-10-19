-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_halfInteger_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/ccbeaaf5-4d10-4f48-acb3-acf7a1218198

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_pos
import Theorems.Thm_CohnElkies_lowerCoth_antitoneOn
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    (k : ℕ) (R : ℝ) :
    AntitoneOn (lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R)
      (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  rw [lowerGammaBoundaryLog_halfInteger k R hy.ne',
    lowerGammaBoundaryLog_halfInteger k R hx.ne']
  simp only [abs_of_pos hx, abs_of_pos hy]
  have hsum :
      (∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (x / 2) ^ 2))) ≤
      ∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hradx :
        0 < ((j : ℝ) + 1 / 2) ^ 2 + (x / 2) ^ 2 := by
      nlinarith [sq_nonneg ((j : ℝ) + 1 / 2),
        sq_pos_of_pos (half_pos hx)]
    apply Real.log_le_log (Real.sqrt_pos.mpr hradx)
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (y / 2 - x / 2),
      mul_nonneg (half_pos hx).le
        (show 0 ≤ y / 2 - x / 2 by linarith)]
  have hxarg : 0 < Real.pi * x / 2 := by positivity
  have hyarg : 0 < Real.pi * y / 2 := by positivity
  have harg : Real.pi * x / 2 ≤ Real.pi * y / 2 := by
    gcongr
  have hcoth :
      lowerCoth (Real.pi * y / 2) ≤
        lowerCoth (Real.pi * x / 2) :=
    lowerCoth_antitoneOn hxarg hyarg harg
  have hratio :
      lowerCoth (Real.pi * y / 2) / (y / 2) ≤
        lowerCoth (Real.pi * x / 2) / (x / 2) := by
    calc
      lowerCoth (Real.pi * y / 2) / (y / 2) ≤
        lowerCoth (Real.pi * x / 2) / (y / 2) :=
        div_le_div_of_nonneg_right hcoth (half_pos hy).le
      _ ≤ lowerCoth (Real.pi * x / 2) / (x / 2) :=
        div_le_div_of_nonneg_left
          (lowerCoth_pos hxarg).le (half_pos hx)
          (by linarith)
  have hcorr :
      Real.log (lowerCoth (Real.pi * y / 2) / (y / 2)) ≤
        Real.log (lowerCoth (Real.pi * x / 2) / (x / 2)) :=
    Real.log_le_log
      (div_pos (lowerCoth_pos hyarg) (half_pos hy)) hratio
  linarith
end CohnElkies
