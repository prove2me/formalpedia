-- Prove2me | solution 1 for CoopetSourcing.WholesalePrice.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T04:57:50.045185+00:00
-- url     : https://prove2.me/submissions/1307b6b8-ffcc-419f-b173-16fe40d42ea3

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

lemma sqrt34_fine : (5.830951 : ℝ) < Real.sqrt 34 ∧ Real.sqrt 34 < 5.830952 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma wALow_gt : (0.004965 : ℝ) < wALow := by
  unfold wALow
  obtain ⟨h1, h2⟩ := sqrt34_fine
  rw [lt_div_iff_of_neg (by nlinarith)]; nlinarith

lemma pool_minus_no_pos (t wA : ℝ) (h : Standing t wA) :
    0 < (10 * t - 7 + 14 * wA) * (60823 - 129730 * t - 221606 * wA +
      Real.sqrt 34 * (22260 * t - 10290 + 7980 * wA)) / 2998800 := by
  obtain ⟨ht, hw1, hw2⟩ := h
  have := wALow_gt
  obtain ⟨s1, s2⟩ := sqrt34_fine
  apply div_pos _ (by norm_num)
  apply mul_pos_of_neg_of_neg
  · linarith
  · nlinarith [mul_pos (show (0:ℝ) < 22260 * Real.sqrt 34 - 129730 by linarith)
      (show (0:ℝ) < 7 / 10 - 7 / 5 * wA - t by linarith)]


lemma poolcap_eq (t wA : ℝ) : profitNo t wA + (10 * t - 7 + 14 * wA) *
        (60823 - 129730 * t - 221606 * wA + Real.sqrt 34 * (22260 * t - 10290 + 7980 * wA))
          / 2998800 = profitPool t wA (wIBar t wA) := by
  have hs : Real.sqrt 34 ^ 2 = 34 := Real.sq_sqrt (by norm_num)
  simp only [profitNo, profitPool, stateProfitVI, poolQO1, poolQO2H, poolQI, noQO2H, noQO2L,
    noQI, wIBar]
  linear_combination (767 * (10 * t + 14 * wA - 7) ^ 2 / 5664400) * hs

lemma profitPool_cont (t wA : ℝ) : Continuous (profitPool t wA) := by
  unfold profitPool; simp only [stateProfitVI, poolQO2H, poolQI, poolQO1]; fun_prop

lemma limit_poolcap (t wA : ℝ) (h : Standing t wA) :
    Filter.Tendsto (profitVI t wA) (nhdsWithin (wIBar t wA) (Set.Iio (wIBar t wA)))
      (nhds (profitPool t wA (wIBar t wA))) := by
  have hlt := sepPool_lt_IBar t wA h
  have h1 : Filter.Tendsto (profitPool t wA) (nhdsWithin (wIBar t wA) (Set.Iio (wIBar t wA)))
      (nhds (profitPool t wA (wIBar t wA))) :=
    ((profitPool_cont t wA).tendsto _).mono_left nhdsWithin_le_nhds
  apply h1.congr'
  have hmem : Set.Ioo (wSepPool t wA) (wIBar t wA) ∈
      nhdsWithin (wIBar t wA) (Set.Iio (wIBar t wA)) := Ioo_mem_nhdsLT hlt
  filter_upwards [hmem] with w hw
  simp only [profitVI, if_neg (not_le.mpr hw.1), if_pos hw.2]

lemma noProfit_lt_poolcap (t wA : ℝ) (h : Standing t wA) :
    profitNo t wA < profitPool t wA (wIBar t wA) := by
  rw [← poolcap_eq]; linarith [pool_minus_no_pos t wA h]

lemma wIBar_pos (t wA : ℝ) (h : Standing t wA) : 0 < wIBar t wA := by
  obtain ⟨ht, hw1, hw2⟩ := h
  have := wALow_pos
  obtain ⟨s1, s2⟩ := sqrt34_bounds
  unfold wIBar
  apply div_pos _ (by norm_num)
  nlinarith [mul_pos (show (0:ℝ) < 35 - 6 * Real.sqrt 34 by linarith)
    (show (0:ℝ) < 7 - 10 * t - 14 * wA by linarith)]

end CSAux


open CoopetSourcing.WholesalePrice

theorem solution (t wA : ℝ) (h : CoopetSourcing.WholesalePrice.Standing t wA) :
    ∃ wI : ℝ, 0 ≤ wI ∧ wI < CoopetSourcing.WholesalePrice.wIBar t wA ∧
      CoopetSourcing.WholesalePrice.profitNo t wA < CoopetSourcing.WholesalePrice.profitVI t wA wI := by
  have hlim := CSAux.limit_poolcap t wA h
  have hgt := CSAux.noProfit_lt_poolcap t wA h
  have hpos := CSAux.wIBar_pos t wA h
  have e1 := hlim.eventually (lt_mem_nhds hgt)
  have e2 : Set.Ioo 0 (wIBar t wA) ∈ nhdsWithin (wIBar t wA) (Set.Iio (wIBar t wA)) :=
    Ioo_mem_nhdsLT hpos
  obtain ⟨w, hw1, hw2⟩ := (e1.and e2).exists
  exact ⟨w, hw2.1.le, hw2.2, hw1⟩
