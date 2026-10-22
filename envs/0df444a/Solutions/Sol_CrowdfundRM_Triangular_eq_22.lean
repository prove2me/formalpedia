-- Prove2me | solution 1 for CrowdfundRM.Triangular.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:46:36.529929+00:00
-- url     : https://prove2.me/submissions/ebf4300f-7ab8-407b-9345-ecc874445534

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

set_option autoImplicit false
open CrowdfundRM.Triangular

theorem solution (M : Campaign) (hM : M.Standing) (hLh : M.Lh = 0) (p T : ℝ) (hT : 0 ≤ T) :
    M.revenue p T = M.Ri p T := by
  have hnph : M.nph p T T = 0 := by
    unfold Campaign.nph; rw [hLh]; simp
  have hsub : ∫ x in (0:ℝ)..T, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x))) =
      Real.exp (-M.k * T) * ∫ x in (0:ℝ)..T, Real.exp (M.k * x) * M.Fbi (p * Real.exp (M.r * x)) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun y : ℝ => Real.exp (-M.k * (T - y)) * M.Fbi (p * Real.exp (M.r * y))) (a := 0) (b := T) T
    simp only [sub_sub_cancel, sub_self, sub_zero] at h
    rw [h, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [show -M.k * (T - y) = -M.k * T + M.k * y by ring, Real.exp_add]
    ring
  unfold Campaign.revenue Campaign.ntot Campaign.Ri Campaign.npi
  rw [hnph, add_zero, hsub]
  ring
