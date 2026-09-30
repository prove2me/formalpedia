-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.coord_profit_concave_max
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:47:14.632874+00:00
-- url     : https://prove2.me/submissions/b813cd76-d786-4f1b-b50e-3ca198500881

import Definitions.Def_FalseFailureReturns_TargetRebate_Model
set_option autoImplicit false
open FalseFailureReturns.TargetRebate

private theorem concave_profit (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ConcaveOn ℝ (Set.Ioi 0) (fun x : ℝ => c*(1-1/x)-a*x^2/2) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [Set.mem_Ioi] at hx hy
  simp only [smul_eq_mul]
  have ht : 0 < u*x+v*y := by
    have hmin : 0 < min x y := lt_min hx hy
    have hxx := mul_le_mul_of_nonneg_left (min_le_left x y) hu
    have hyy := mul_le_mul_of_nonneg_left (min_le_right x y) hv
    nlinarith
  have he : (c*(1-1/(u*x+v*y))-a*(u*x+v*y)^2/2) -
      (u*(c*(1-1/x)-a*x^2/2)+v*(c*(1-1/y)-a*y^2/2)) =
      u*v*(x-y)^2*(c/(x*y*(u*x+v*y))+a/2) := by
    have hv' : v = 1-u := by linarith
    rw [hv'] at ht ⊢
    field_simp
    ring
  apply sub_nonneg.mp
  rw [he]
  positivity

private theorem maximal_profit (a c r : ℝ) (ha : 0 ≤ a) (hr : 0 < r)
    (hcube : a*r^3=c) :
    IsMaxOn (fun x : ℝ => c*(1-1/x)-a*x^2/2) (Set.Ioi 0) r := by
  intro y hy
  change c*(1-1/y)-a*y^2/2 ≤ c*(1-1/r)-a*r^2/2
  have hy' : 0 < y := hy
  have he : (c*(1-1/r)-a*r^2/2) - (c*(1-1/y)-a*y^2/2) =
      a*(y-r)^2*(y+2*r)/(2*y) := by
    rw [← hcube]
    field_simp
    ring
  apply sub_nonneg.mp
  rw [he]
  positivity

theorem solution (P : Params)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr) :
    ConcaveOn ℝ (Set.Ioi 0) (coordProfit P) ∧
      IsMaxOn (coordProfit P) (Set.Ioi 0) (coordEffort P) := by
  constructor
  · exact concave_profit P.a ((P.Mm+P.Rr)*P.β) ha.le (by positivity)
  · apply maximal_profit P.a ((P.Mm+P.Rr)*P.β) (coordEffort P) ha.le
    · unfold coordEffort
      positivity
    · unfold coordEffort
      rw [← Real.rpow_mul_natCast (by positivity)]
      norm_num
      field_simp
