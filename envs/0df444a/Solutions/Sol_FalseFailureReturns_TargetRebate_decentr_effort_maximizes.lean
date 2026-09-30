-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.decentr_effort_maximizes
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:48:55.929393+00:00
-- url     : https://prove2.me/submissions/8fd18ced-3b62-4f18-bf1d-ddc3f0c5ca8d

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
    IsMaxOn (retailerProfit P) (Set.Ici 1) (decentrEffort P) := by
  let c := P.Rr*P.β
  let r := (c/P.a)^((1:ℝ)/3)
  have hc : 0 < c := by dsimp [c]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hcube : P.a*r^3=c := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
    field_simp
  have he : retailerProfit P = (fun x : ℝ => c*(1-1/x)-P.a*x^2/2) := by
    funext x
    dsimp [retailerProfit, c]
    ring
  rw [he]
  change IsMaxOn (fun x : ℝ => c*(1-1/x)-P.a*x^2/2) (Set.Ici 1) (max r 1)
  by_cases hcase : 1 ≤ r
  · rw [max_eq_left hcase]
    intro y hy
    exact maximal_profit P.a c r ha.le hr hcube (by change 0 < y; exact lt_of_lt_of_le zero_lt_one hy)
  · have hrle : r ≤ 1 := le_of_not_ge hcase
    rw [max_eq_right hrle]
    have hr3 : r^3 ≤ 1 := by nlinarith [pow_le_pow_left₀ hr.le hrle 3]
    have hca : c ≤ P.a := by nlinarith [mul_le_mul_of_nonneg_left hr3 ha.le]
    intro y hy
    have hy' : 1 ≤ y := hy
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy'
    have hterm : 0 ≤ P.a*y*(y+1)-2*c := by
      have hyy : 2 ≤ y*(y+1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hyy ha.le]
    have hid : (c*(1-1/(1:ℝ))-P.a*1^2/2) - (c*(1-1/y)-P.a*y^2/2) =
        (y-1)*(P.a*y*(y+1)-2*c)/(2*y) := by
      field_simp
      ring
    change c*(1-1/y)-P.a*y^2/2 ≤ c*(1-1/(1:ℝ))-P.a*1^2/2
    apply sub_nonneg.mp
    rw [hid]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hy') hterm) (by positivity)
