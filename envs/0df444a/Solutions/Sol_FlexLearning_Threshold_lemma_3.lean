-- Prove2me | solution 1 for FlexLearning.Threshold.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:35:31.624929+00:00
-- url     : https://prove2.me/submissions/09ae8836-33d6-4e1b-8ea6-7999a3c92ff2

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

open FlexLearning.Threshold MeasureTheory

namespace FlexLAux

lemma prior_integral (x U : ℝ) (hU : 0 < U) (f : ℝ → ℝ) :
    ∫ d, f d ∂(prior x U) = U⁻¹ * ∫ d in x..x + U, f d := by
  unfold prior
  rw [integral_smul_measure, intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc]
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal hU.le]

lemma int_min (x U Q : ℝ) (hU : 0 < U) :
    ∫ d in x..x + U, min d Q =
      if Q ≤ x then Q * U
      else if Q ≤ x + U then x * U + (Q - x) * U - (Q - x) ^ 2 / 2
      else x * U + U ^ 2 / 2 := by
  split_ifs with h1 h2
  · rw [intervalIntegral.integral_congr (g := fun _ => Q)]
    · simp; ring
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      simp only
      exact min_eq_right (by linarith [hd.1])
  · have hc : Continuous fun d : ℝ => min d Q := continuous_id.min continuous_const
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := Q)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (g := fun d => d) (a := x) (b := Q),
      intervalIntegral.integral_congr (g := fun _ => Q) (a := Q) (b := x + U)]
    · simp [integral_id]; ring
    · intro d hd
      rw [Set.uIcc_of_le h2] at hd
      exact min_eq_right hd.1
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      exact min_eq_left hd.2
  · rw [intervalIntegral.integral_congr (g := fun d => d)]
    · simp [integral_id]; ring
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      exact min_eq_left (by linarith [hd.2])

lemma nv_formula (p c x U Q : ℝ) (hU : 0 < U) :
    nvProfit p c (prior x U) Q =
      p * U⁻¹ * (if Q ≤ x then Q * U
      else if Q ≤ x + U then x * U + (Q - x) * U - (Q - x) ^ 2 / 2
      else x * U + U ^ 2 / 2) - c * Q := by
  unfold nvProfit
  rw [prior_integral x U hU, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    int_min x U Q hU]
  · split_ifs <;> simp <;> field_simp <;> ring
  · exact ((continuous_id.min continuous_const).const_smul p).intervalIntegrable _ _
  · exact intervalIntegrable_const

end FlexLAux

open FlexLAux in
theorem solution (p c x U : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    0 ≤ x + U * ((p - c) / p) ∧
    nvProfit p c (prior x U) (x + U * ((p - c) / p)) = (p - c) * x + U / 2 * ((p - c) ^ 2 / p) ∧
    ∀ Q : ℝ, 0 ≤ Q →
      nvProfit p c (prior x U) Q ≤ nvProfit p c (prior x U) (x + U * ((p - c) / p)) := by
  have hp : 0 < p := by linarith
  have hr0 : 0 ≤ (p - c) / p := div_nonneg (by linarith) hp.le
  have hr1 : (p - c) / p ≤ 1 := by rw [div_le_one hp]; linarith
  have hr0' : 0 < (p - c) / p := div_pos (by linarith) hp
  have hval : nvProfit p c (prior x U) (x + U * ((p - c) / p)) =
      (p - c) * x + U / 2 * ((p - c) ^ 2 / p) := by
    rw [nv_formula p c x U _ hU]
    rw [if_neg (by nlinarith), if_pos (by nlinarith)]
    field_simp; ring
  refine ⟨by positivity, hval, ?_⟩
  intro Q hQ
  rw [hval, nv_formula p c x U Q hU]
  split_ifs with h1 h2
  · field_simp
    nlinarith [mul_nonneg (sub_nonneg.2 hcp.le) (sub_nonneg.2 h1), sq_nonneg (p - c)]
  · -- interior: concave quadratic
    have key : p * U⁻¹ * (x * U + (Q - x) * U - (Q - x) ^ 2 / 2) - c * Q =
        (p - c) * x + U / 2 * ((p - c) ^ 2 / p) - p / (2 * U) * (Q - x - U * ((p - c) / p)) ^ 2 := by
      field_simp; ring
    rw [key]
    have : 0 ≤ p / (2 * U) * (Q - x - U * ((p - c) / p)) ^ 2 := by positivity
    linarith
  · push Not at h1 h2
    have key : p * U⁻¹ * (x * U + U ^ 2 / 2) - c * Q = p * x + p * U / 2 - c * Q := by
      field_simp
    rw [key]
    have : (p - c) * x + U / 2 * ((p - c) ^ 2 / p) - (p * x + p * U / 2 - c * (x + U)) =
        U / 2 * c ^ 2 / p := by field_simp; ring
    have h3 : 0 ≤ U / 2 * c ^ 2 / p := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2.le hc]
