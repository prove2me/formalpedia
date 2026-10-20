-- Prove2me | solution 1 for CoopetSourcing.WholesalePrice.lemma_3_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T04:55:05.828073+00:00
-- url     : https://prove2.me/submissions/dee47f14-723d-456a-b72e-713e88181725

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

open CoopetSourcing.WholesalePrice

namespace CSAux

lemma sqrt34_bounds : (5.83 : ℝ) < Real.sqrt 34 ∧ Real.sqrt 34 < 5.831 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma tLow_gt : (0.28 : ℝ) < tLow := by
  unfold tLow
  have : (1.414 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [lt_div_iff₀ (by norm_num)]; nlinarith

lemma wALow_pos : 0 < wALow := by
  unfold wALow
  obtain ⟨h1, h2⟩ := sqrt34_bounds
  apply div_pos_of_neg_of_neg <;> nlinarith

lemma sepPool_lt_IBar (t wA : ℝ) (h : Standing t wA) : wSepPool t wA < wIBar t wA := by
  obtain ⟨ht, hw1, hw2⟩ := h
  have ht' := tLow_gt
  have hw0 := wALow_pos
  obtain ⟨s1, s2⟩ := sqrt34_bounds
  set s := Real.sqrt 34
  unfold wSepPool wIBar
  set Q := 6 * (25 * (1 - 2 * wA) ^ 2 + 6064 * t ^ 2 - 320 * t * (1 - 2 * wA))
  set R := 1500 * ((245 - 350 * t - 70 * wA - 6 * s * (7 - 10 * t - 14 * wA)) / 420)
      - (1620 * wA - 3426 * t - 60)
  have hR : 0 < R := by simp only [R]; nlinarith
  have hsq : 17 * Real.sqrt Q < R := by
    have : 17 * Real.sqrt Q = Real.sqrt (289 * Q) := by
      have h17 : Real.sqrt 289 = 17 := by
        rw [show (289:ℝ) = 17 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 289) Q, h17]
    rw [this, Real.sqrt_lt' hR]
    have hA : 0 < 60 * (1 - 2 * wA) + 3426 * t := by linarith
    have hB : 0 ≤ (25 / 7) * (35 - 6 * s) * (7 - 10 * t - 14 * wA) := by
      apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)); linarith
    have hRe : R = (60 * (1 - 2 * wA) + 3426 * t) + (25 / 7) * (35 - 6 * s) * (7 - 10 * t - 14 * wA) := by
      simp only [R]; ring
    have hu : 0 < 1 - 2 * wA := by linarith
    have hu1 : 1 - 2 * wA < 1 := by linarith
    have key : 289 * Q < (60 * (1 - 2 * wA) + 3426 * t) ^ 2 := by
      simp only [Q]
      nlinarith [mul_pos hu (show (0:ℝ) < t by linarith), mul_pos hu (sub_pos.mpr hu1),
        mul_pos (show (0:ℝ) < t by linarith) (show (0:ℝ) < t by linarith)]
    rw [hRe]; nlinarith
  have : 1620 * wA - 3426 * t - 60 + 17 * Real.sqrt Q < 1500 *
      ((245 - 350 * t - 70 * wA - 6 * s * (7 - 10 * t - 14 * wA)) / 420) := by
    simp only [R] at hsq; linarith
  linarith

end CSAux

theorem solution (t wA : ℝ) (h : CoopetSourcing.WholesalePrice.Standing t wA) :
    Filter.Tendsto (CoopetSourcing.WholesalePrice.profitVI t wA)
      (nhdsWithin (CoopetSourcing.WholesalePrice.wIBar t wA)
        (Set.Iio (CoopetSourcing.WholesalePrice.wIBar t wA)))
      (nhds (CoopetSourcing.WholesalePrice.profitNo t wA + (10 * t - 7 + 14 * wA) *
        (60823 - 129730 * t - 221606 * wA + Real.sqrt 34 * (22260 * t - 10290 + 7980 * wA))
          / 2998800)) := by
  have hlt := CSAux.sepPool_lt_IBar t wA h
  have hval : profitNo t wA + (10 * t - 7 + 14 * wA) *
        (60823 - 129730 * t - 221606 * wA + Real.sqrt 34 * (22260 * t - 10290 + 7980 * wA))
          / 2998800 = profitPool t wA (wIBar t wA) := by
    have hs : Real.sqrt 34 ^ 2 = 34 := Real.sq_sqrt (by norm_num)
    simp only [profitNo, profitPool, stateProfitVI, poolQO1, poolQO2H, poolQI, noQO2H, noQO2L,
      noQI, wIBar]
    linear_combination (767 * (10 * t + 14 * wA - 7) ^ 2 / 5664400) * hs
  rw [hval]
  have hcont : Continuous (profitPool t wA) := by
    unfold profitPool; simp only [stateProfitVI, poolQO2H, poolQI, poolQO1]; fun_prop
  have h1 : Filter.Tendsto (profitPool t wA) (nhdsWithin (wIBar t wA) (Set.Iio (wIBar t wA)))
      (nhds (profitPool t wA (wIBar t wA))) :=
    (hcont.tendsto _).mono_left nhdsWithin_le_nhds
  apply h1.congr'
  have hmem : Set.Ioo (wSepPool t wA) (wIBar t wA) ∈
      nhdsWithin (wIBar t wA) (Set.Iio (wIBar t wA)) := Ioo_mem_nhdsLT hlt
  filter_upwards [hmem] with w hw
  simp only [profitVI, if_neg (not_le.mpr hw.1), if_pos hw.2]
