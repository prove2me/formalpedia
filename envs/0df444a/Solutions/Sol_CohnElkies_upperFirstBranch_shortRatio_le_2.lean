-- Prove2me | solution 2 for CohnElkies.upperFirstBranch_shortRatio_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:36:31.677964+00:00
-- url     : https://prove2.me/submissions/736a0b35-7ed2-48ff-a0bc-8e6db33f6326

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
    {ε u a : ℝ}
    (hε : 0 < ε) (ha : 0 ≤ a)
    (hulower : -1 ≤ u)
    (huupper : u ≤ 1 + ε / 2)
    (hmargin : 0 ≤ shortMargin ε a) :
    shortMargin ε a *
        Real.exp ((u - 1) * a) *
          (Real.cosh (u * a) / Real.cosh a) ≤
      1 - 4 * ε := by
  unfold shortMargin at hmargin ⊢
  set b : ℝ := 1 + ε / 2 with hb
  have hcpos : 0 < Real.cosh a := Real.cosh_pos a
  have h1 : Real.cosh (u * a) ≤ Real.cosh (b * a) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_pos (show (0:ℝ) < b by rw [hb]; linarith)]
    apply mul_le_mul_of_nonneg_right _ ha
    rw [abs_le]; constructor <;> linarith
  have h2 : Real.cosh (b * a) ≤ Real.exp ((b - 1) * a) * Real.cosh a := by
    rw [Real.cosh_eq, Real.cosh_eq]
    have he : Real.exp (-(b * a)) ≤ Real.exp ((b - 1) * a) * Real.exp (-a) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; rw [hb]; nlinarith
    have he2 : Real.exp (b * a) = Real.exp ((b - 1) * a) * Real.exp a := by
      rw [← Real.exp_add]; ring_nf
    rw [he2]; nlinarith [Real.exp_pos ((b - 1) * a)]
  have h3 : Real.exp ((u - 1) * a) ≤ Real.exp ((ε / 2) * a) := by
    apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonneg_right _ ha; linarith
  have hR : Real.exp ((u - 1) * a) * (Real.cosh (u * a) / Real.cosh a) ≤ Real.exp (ε * a) := by
    rw [mul_div_assoc', div_le_iff₀ hcpos]
    calc Real.exp ((u - 1) * a) * Real.cosh (u * a)
        ≤ Real.exp ((ε / 2) * a) * (Real.exp ((b - 1) * a) * Real.cosh a) := by
          apply mul_le_mul h3 (h1.trans h2) (Real.cosh_pos _).le (Real.exp_pos _).le
      _ = Real.exp (ε * a) * Real.cosh a := by
          rw [← mul_assoc, ← Real.exp_add]; rw [hb]; ring_nf
  have ht0 : 0 ≤ ε * a := mul_nonneg hε.le ha
  have ht1 : ε * a < 1 := by nlinarith
  have hexp := Real.exp_bound_div_one_sub_of_interval ht0 ht1
  have hM : 0 ≤ 1 - 10 * ε * (1 + a) := hmargin
  calc (1 - 10 * ε * (1 + a)) * Real.exp ((u - 1) * a) * (Real.cosh (u * a) / Real.cosh a)
      = (1 - 10 * ε * (1 + a)) * (Real.exp ((u - 1) * a) * (Real.cosh (u * a) / Real.cosh a)) := by ring
    _ ≤ (1 - 10 * ε * (1 + a)) * (1 / (1 - ε * a)) :=
        mul_le_mul_of_nonneg_left (hR.trans hexp) hM
    _ ≤ 1 - 4 * ε := by
        rw [mul_one_div, div_le_iff₀ (by linarith)]
        nlinarith

