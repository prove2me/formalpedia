-- Prove2me | solution 1 for CrowdContest.Pooling.concave_deriv_inverse
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:14:56.585187+00:00
-- url     : https://prove2.me/submissions/9ff615fb-2ade-424d-9659-e85977ec58cd

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

set_option autoImplicit false
open MeasureTheory CrowdContest.Pooling

theorem solution (C : ℝ → ℝ) (hC : IsCost C)
    (hconv : ConvexOn ℝ (Set.Ioi 0) (deriv C)) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (habc : deriv C c = (deriv C a + deriv C b) / 2) :
    a + b ≤ 2 * c := by
  have hcd : ContDiffOn ℝ 1 (deriv C) (Set.Ioi 0) :=
    hC.2.1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hmono : StrictMonoOn (deriv C) (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0) hcd.continuousOn
    intro x hx
    rw [interior_Ioi] at hx
    exact (hC.2.2 x hx).2
  have hm : (0:ℝ) < (1/2 : ℝ) • a + (1/2 : ℝ) • b := by
    simp only [smul_eq_mul]; linarith
  have h1 := hconv.2 (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 hb) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h1 hm
  by_contra hlt
  push_neg at hlt
  have hlt' : c < 1/2 * a + 1/2 * b := by linarith
  have := hmono (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hm) hlt'
  linarith
