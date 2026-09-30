-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.retailer_gain_corner
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:33:00.215886+00:00
-- url     : https://prove2.me/submissions/680f4d83-ee8b-421a-9100-adf9e7798373

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
open MeasureTheory Set
open FalseFailureReturns.TargetRebate
private lemma shortfall_formula (β ρ T : ℝ) (hβ : 0 < β) (hρ : 0 < ρ)
    (hT0 : 0 ≤ T) (hT : T ≤ 2*β/ρ) : expShortfall β ρ T = T^2*ρ/(4*β) := by
  let B := 2*β/ρ
  have hB : 0 < B := by dsimp [B]; positivity
  have hf : Continuous (fun x : ℝ => max (T-x) 0) := by fun_prop
  have hi : ∫ x in Icc (0:ℝ) B, max (T-x) 0 = T^2/2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hB.le]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 T)
      (hf.intervalIntegrable T B)]
    have hleft : ∫ x in (0:ℝ)..T, max (T-x) 0 = ∫ x in (0:ℝ)..T, T-x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hT0] at hx
      exact max_eq_left (by linarith [hx.2])
    have hright : ∫ x in T..B, max (T-x) 0 = 0 := by
      calc
        _ = ∫ x in T..B, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hT] at hx
          exact max_eq_right (by linarith [hx.1])
        _ = 0 := by simp
    have hc : IntervalIntegrable (fun _ : ℝ => T) volume 0 T := continuous_const.intervalIntegrable _ _
    have hid : IntervalIntegrable (fun x : ℝ => x) volume 0 T := continuous_id.intervalIntegrable _ _
    rw [hleft, hright, add_zero, intervalIntegral.integral_sub hc hid,
      intervalIntegral.integral_const, integral_id]
    ring
  unfold expShortfall uniformLaw ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal hB.le, smul_eq_mul]
  change B⁻¹ * (∫ x in Icc (0:ℝ) B, max (T-x) 0) = _
  rw [hi]
  dsimp [B]
  field_simp
  ring

open Filter Topology
private lemma rebate_derivative (P : Params) (T u r : ℝ) (hβ : 0 < P.β) (hr : 0 < r)
    (hT0 : 0 ≤ T) (hT : T < 2*P.β/r) :
    HasDerivAt (rebateRetailerProfit P T u)
      (T^2*u/(4*P.β)-P.a*r+P.Rr*P.β/r^2) r := by
  have he : rebateRetailerProfit P T u =ᶠ[𝓝 r]
      (fun x : ℝ => T^2*u*x/(4*P.β)-P.a*x^2/2+P.Rr*P.β*(1-1/x)) := by
    have hmul : T*r < 2*P.β := (lt_div_iff₀ hr).mp hT
    have hc : Continuous (fun x : ℝ => 2*P.β-T*x) := by fun_prop
    filter_upwards [eventually_gt_nhds hr, hc.continuousAt.eventually (eventually_gt_nhds (by linarith : 0 < 2*P.β-T*r))] with x hx htx
    rw [rebateRetailerProfit, shortfall_formula _ _ _ hβ hx hT0 ((le_div_iff₀ hx).mpr (by linarith))]
    ring
  have hd := (((hasDerivAt_id r).const_mul (T^2*u)).div_const (4*P.β)).sub
    ((((hasDerivAt_id r).pow 2).const_mul P.a).div_const 2)
  have hi := ((((hasDerivAt_const r (1:ℝ)).div (hasDerivAt_id r) hr.ne').const_sub 1).const_mul (P.Rr*P.β))
  have hd' : HasDerivAt
      (fun x : ℝ => T^2*u*x/(4*P.β)-P.a*x^2/2+P.Rr*P.β*(1-1/x))
      (T^2*u/(4*P.β)-P.a*r+P.Rr*P.β/r^2) r := by
    convert! hd.add hi using 1 <;> first | rfl | (funext x; rfl) | (dsimp; ring)
  exact hd'.congr_of_eventuallyEq he
private lemma rebate_foc (P : Params) (T u r : ℝ) (hβ : 0 < P.β)
    (hT0 : 0 ≤ T) (hr : 1 < r)
    (hmax : IsMaxOn (rebateRetailerProfit P T u) (Set.Ici 1) r)
    (hT : T < 2*P.β/r) :
    T^2*u*r^2-4*P.a*P.β*r^3+4*P.Rr*P.β^2=0 := by
  have hd := rebate_derivative P T u r hβ (by linarith) hT0 hT
  have hm : IsLocalMax (rebateRetailerProfit P T u) r := hmax.isLocalMax (Ici_mem_nhds hr)
  have hz : T^2*u/(4*P.β)-P.a*r+P.Rr*P.β/r^2=0 := hd.deriv.symm.trans hm.deriv_eq_zero
  have hr0 : r ≠ 0 := by linarith
  field_simp [hr0, hβ.ne'] at hz
  nlinarith [hz]

private lemma coord_gt (P : Params) (ha : 0 < P.a)
    (hint : P.a < (P.Mm+P.Rr)*P.β) : 1 < coordEffort P := by
  apply Real.one_lt_rpow _ (by norm_num)
  rw [div_mul_eq_mul_div, one_lt_div ha]
  exact hint
private lemma coord_cube (P : Params) (ha : 0 < P.a) (hβ : 0 < P.β)
    (hM : 0 < P.Mm) (hR : 0 < P.Rr) :
    P.a * coordEffort P ^ 3 = (P.Mm+P.Rr)*P.β := by
  unfold coordEffort
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num
  field_simp
private lemma coord_charge (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm+P.Rr)*P.β) (hT : 0 < T)
    (hTlt : T < 2*P.β/coordEffort P) (hcoord : Coordinates P T u) :
    u*expShortfall P.β (coordEffort P) T = P.Mm*P.β/coordEffort P := by
  have hc := coord_gt P ha hint
  have hcpos : 0 < coordEffort P := by linarith
  have hcb := coord_cube P ha hβ hM hR
  have hcb' := congrArg (fun x : ℝ => 4*P.β*x) hcb
  have hf := rebate_foc P T u (coordEffort P) hβ hT.le hc hcoord hTlt
  rw [shortfall_formula _ _ _ hβ hcpos hT.le hTlt.le]
  field_simp [hcpos.ne',hβ.ne']
  nlinarith [hcb',hf]
private lemma manufacturer_at_coord (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm+P.Rr)*P.β) (hT : 0 < T)
    (hTlt : T < 2*P.β/coordEffort P) (hcoord : Coordinates P T u) :
    rebateManufProfit P T u (coordEffort P) = P.Mm*P.β*((coordEffort P-2)/coordEffort P) := by
  rw [rebateManufProfit,coord_charge P T u ha hβ hM hR hint hT hTlt hcoord]
  have hcpos : 0 < coordEffort P := lt_trans zero_lt_one (coord_gt P ha hint)
  field_simp [hcpos.ne']
  ring
private lemma retailer_at_coord (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm+P.Rr)*P.β) (hT : 0 < T)
    (hTlt : T < 2*P.β/coordEffort P) (hcoord : Coordinates P T u) :
    rebateRetailerProfit P T u (coordEffort P) =
      P.β*(P.Mm-3*P.Rr)/(2*coordEffort P)+P.Rr*P.β := by
  rw [rebateRetailerProfit,coord_charge P T u ha hβ hM hR hint hT hTlt hcoord]
  have hcpos : 0 < coordEffort P := lt_trans zero_lt_one (coord_gt P ha hint)
  have hcb := coord_cube P ha hβ hM hR
  field_simp [hcpos.ne']
  nlinarith [hcb]
private lemma retailer_gain (P : Params) (T u : ℝ) (hu : 0 ≤ u)
    (hcoord : Coordinates P T u) :
    retailerProfit P (decentrEffort P) ≤ rebateRetailerProfit P T u (coordEffort P) := by
  have hd : decentrEffort P ∈ Ici (1:ℝ) := by
    simp only [Set.mem_Ici, decentrEffort]
    exact le_max_right _ _
  have hh := hcoord hd
  have hn : 0 ≤ expShortfall P.β (decentrEffort P) T := integral_nonneg (fun x => le_max_right _ _)
  have hu' := mul_nonneg hu hn
  dsimp [rebateRetailerProfit,retailerProfit] at hh ⊢
  linarith

theorem solution (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) (hu : 0 < u) (hT : 0 < T)
    (hTlt : T < 2 * P.β / coordEffort P) (hcoord : Coordinates P T u)
    (hD : decentrEffort P = 1) :
    0 ≤ rebateRetailerProfit P T u (coordEffort P) - retailerProfit P (decentrEffort P) := by
  exact sub_nonneg.mpr (retailer_gain P T u hu.le hcoord)
