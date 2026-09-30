-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.rebate_first_order_condition
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:27:43.934964+00:00
-- url     : https://prove2.me/submissions/cf72cece-e03b-4226-9901-febc77af5651

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

theorem solution (P : Params) (T u ρs : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hu : 0 < u) (hT : 0 < T) (hρs : 1 < ρs)
    (hmax : IsMaxOn (rebateRetailerProfit P T u) (Set.Ici 1) ρs)
    (hTlt : T < 2 * P.β / ρs) :
    T ^ 2 * u * ρs ^ 2 - 4 * P.a * P.β * ρs ^ 3 + 4 * P.Rr * P.β ^ 2 = 0 :=
  rebate_foc P T u ρs hβ hT.le hρs hmax hTlt
