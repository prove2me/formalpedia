-- Prove2me | solution 1 for DrugMarket.repression_success_monotone
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:06:11.746078+00:00
-- url     : https://prove2.me/submissions/5f60526a-35d4-4d37-904e-8528e08b9a96

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem repression_success_monotone (q v_r v_i : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hvr : 0 < v_r) (hvi : 0 < v_i) :
  deriv (fun vr => catchRetail q vr v_i) v_r > 0 ∧ deriv (fun vi => catchRetail q v_r vi) v_i < 0 := by
  obtain ⟨hq0, hq1⟩ := hq
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  unfold catchRetail
  constructor
  · have hin : HasDerivAt (fun vr : ℝ => v_i / vr) ((0 * v_r - v_i * 1) / v_r ^ 2) v_r :=
      (hasDerivAt_const v_r v_i).div (hasDerivAt_id' v_r) (ne_of_gt hvr)
    have h := (Real.hasStrictDerivAt_const_rpow hq0 (v_i / v_r)).hasDerivAt.comp v_r hin
    have e : (fun vr : ℝ => Real.rpow q (v_i / vr)) = (fun y : ℝ => q ^ y) ∘ (fun vr : ℝ => v_i / vr) := by
      funext vr; simp [Real.rpow_eq_pow]
    rw [e, h.deriv]
    have hp : 0 < q ^ (v_i / v_r) := Real.rpow_pos_of_pos hq0 _
    have hd : (0 * v_r - v_i * 1) / v_r ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp hlog) hd
  · have hin : HasDerivAt (fun vi : ℝ => vi / v_r) (1 / v_r) v_i :=
      (hasDerivAt_id' v_i).div_const v_r
    have h := (Real.hasStrictDerivAt_const_rpow hq0 (v_i / v_r)).hasDerivAt.comp v_i hin
    have e : (fun vi : ℝ => Real.rpow q (vi / v_r)) = (fun y : ℝ => q ^ y) ∘ (fun vi : ℝ => vi / v_r) := by
      funext vi; simp [Real.rpow_eq_pow]
    rw [e, h.deriv]
    have hp : 0 < q ^ (v_i / v_r) := Real.rpow_pos_of_pos hq0 _
    have hd : 0 < 1 / v_r := by positivity
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hlog) hd

end DrugMarket

open DrugMarket in
theorem solution (q v_r v_i : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hvr : 0 < v_r) (hvi : 0 < v_i) :
  deriv (fun vr => catchRetail q vr v_i) v_r > 0 ∧ deriv (fun vi => catchRetail q v_r vi) v_i < 0 := by
  obtain ⟨hq0, hq1⟩ := hq
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  unfold catchRetail
  constructor
  · have hin : HasDerivAt (fun vr : ℝ => v_i / vr) ((0 * v_r - v_i * 1) / v_r ^ 2) v_r :=
      (hasDerivAt_const v_r v_i).div (hasDerivAt_id' v_r) (ne_of_gt hvr)
    have h := (Real.hasStrictDerivAt_const_rpow hq0 (v_i / v_r)).hasDerivAt.comp v_r hin
    have e : (fun vr : ℝ => Real.rpow q (v_i / vr)) = (fun y : ℝ => q ^ y) ∘ (fun vr : ℝ => v_i / vr) := by
      funext vr; simp [Real.rpow_eq_pow]
    rw [e, h.deriv]
    have hp : 0 < q ^ (v_i / v_r) := Real.rpow_pos_of_pos hq0 _
    have hd : (0 * v_r - v_i * 1) / v_r ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp hlog) hd
  · have hin : HasDerivAt (fun vi : ℝ => vi / v_r) (1 / v_r) v_i :=
      (hasDerivAt_id' v_i).div_const v_r
    have h := (Real.hasStrictDerivAt_const_rpow hq0 (v_i / v_r)).hasDerivAt.comp v_i hin
    have e : (fun vi : ℝ => Real.rpow q (vi / v_r)) = (fun y : ℝ => q ^ y) ∘ (fun vi : ℝ => vi / v_r) := by
      funext vi; simp [Real.rpow_eq_pow]
    rw [e, h.deriv]
    have hp : 0 < q ^ (v_i / v_r) := Real.rpow_pos_of_pos hq0 _
    have hd : 0 < 1 / v_r := by positivity
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hlog) hd
