-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.uniform_rebate_profit
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:27:43.115445+00:00
-- url     : https://prove2.me/submissions/62533b4d-39c8-4790-9983-c57cc8274a8c

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

theorem solution (P : Params) (T u ρ : ℝ)
    (hβ : 0 < P.β) (hρ : 0 < ρ) (hT0 : 0 ≤ T) (hT : T ≤ 2 * P.β / ρ) :
    expShortfall P.β ρ T = T ^ 2 * ρ / (4 * P.β) ∧
      rebateRetailerProfit P T u ρ =
        T ^ 2 * u * ρ / (4 * P.β) - P.a * ρ ^ 2 / 2 + P.Rr * P.β * (1 - 1 / ρ) := by
  refine ⟨shortfall_formula _ _ _ hβ hρ hT0 hT, ?_⟩
  rw [rebateRetailerProfit, shortfall_formula _ _ _ hβ hρ hT0 hT]
  ring
