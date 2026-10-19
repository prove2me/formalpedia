-- Prove2me | solution 1 for CohnElkies.upperFirstBranch_shortRatio_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/195b0b89-9cab-4463-b2cf-d61a6bc85654

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperShortMargin_mul_exp_le_zero_value

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
    {ε u a : ℝ}
    (hε : 0 < ε) (ha : 0 ≤ a)
    (hulower : -1 ≤ u)
    (huupper : u ≤ 1 + ε / 2)
    (hmargin : 0 ≤ shortMargin ε a) :
    shortMargin ε a *
        Real.exp ((u - 1) * a) *
          (Real.cosh (u * a) / Real.cosh a) ≤
      1 - 4 * ε := by
  have hmarginupper :
      shortMargin ε a ≤ 1 - 10 * ε := by
    unfold shortMargin
    nlinarith [mul_nonneg hε.le ha]
  by_cases hubounded : u ≤ 1
  · have huexp :
        Real.exp ((u - 1) * a) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hubounded) ha
    have huabs : |u| ≤ 1 :=
      (abs_le).mpr ⟨hulower, hubounded⟩
    have hcosh : Real.cosh (u * a) ≤ Real.cosh a := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_mul, abs_of_nonneg ha]
      exact (mul_le_mul_of_nonneg_right huabs ha).trans
        (by simp)
    have hratio :
        Real.cosh (u * a) / Real.cosh a ≤ 1 := by
      exact (div_le_one (Real.cosh_pos a)).mpr hcosh
    calc
      shortMargin ε a *
          Real.exp ((u - 1) * a) *
            (Real.cosh (u * a) / Real.cosh a) ≤
        shortMargin ε a * 1 * 1 := by
          gcongr
      _ = shortMargin ε a := by ring
      _ ≤ 1 - 10 * ε := hmarginupper
      _ ≤ 1 - 4 * ε := by linarith
  · have hugreater : 1 ≤ u :=
      (le_of_not_ge hubounded)
    have hδ : 0 ≤ u - 1 := by linarith
    have hratio :
        Real.cosh (u * a) / Real.cosh a ≤
          Real.exp ((u - 1) * a) := by
      convert! cosh_ratio_upper ha hδ using 1; ring_nf
    have hdouble :
        Real.exp (2 * (u - 1) * a) ≤
          Real.exp (ε * a) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg
        (show 0 ≤ ε - 2 * (u - 1) by linarith)
        ha]
    calc
      shortMargin ε a *
          Real.exp ((u - 1) * a) *
            (Real.cosh (u * a) / Real.cosh a) ≤
        shortMargin ε a *
          Real.exp ((u - 1) * a) *
            Real.exp ((u - 1) * a) := by
          gcongr
      _ = shortMargin ε a *
          Real.exp (2 * (u - 1) * a) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      _ ≤ shortMargin ε a *
          Real.exp (ε * a) :=
        mul_le_mul_of_nonneg_left hdouble hmargin
      _ ≤ 1 - 10 * ε :=
        upperShortMargin_mul_exp_le_zero_value
          hε ha
      _ ≤ 1 - 4 * ε := by linarith
end CohnElkies
