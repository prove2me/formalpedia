-- Prove2me | solution 1 for CoopetSourcing.WholesalePrice.lemma_5_gap_mono
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:47:18.389318+00:00
-- url     : https://prove2.me/submissions/59cbc9f0-6059-4e8c-8e7c-a5c8e07a0873

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



namespace CSAux

noncomputable def Qf (t wA : ℝ) : ℝ := 6 * (25 * (1 - 2 * wA) ^ 2 + 6064 * t ^ 2 - 320 * t * (1 - 2 * wA))
noncomputable def Rf (t wA : ℝ) : ℝ := Real.sqrt (Qf t wA)

lemma Qf_nonneg (t wA : ℝ) : 0 ≤ Qf t wA := by unfold Qf; nlinarith [sq_nonneg (5 * (1 - 2 * wA) - 32 * t)]
lemma Rf_nonneg (t wA : ℝ) : 0 ≤ Rf t wA := Real.sqrt_nonneg _
lemma Rf_sq (t wA : ℝ) : Rf t wA ^ 2 = Qf t wA := Real.sq_sqrt (Qf_nonneg t wA)
lemma Rf_ge (t wA : ℝ) (ht : 0 ≤ t) : 173.8 * t ≤ Rf t wA := by
  unfold Rf; rw [Real.le_sqrt (by positivity) (Qf_nonneg t wA)]; unfold Qf
  nlinarith [sq_nonneg (5 * (1 - 2 * wA) - 32 * t)]

lemma wSepPool_eq (t wA : ℝ) : wSepPool t wA = (1620 * wA - 3426 * t - 60 + 17 * Rf t wA) / 1500 := rfl

lemma std_facts (t wA : ℝ) (h : Standing t wA) : 0.28 < t ∧ 0.004965 < wA ∧ wA < 1 / 2 - 5 * t / 7 :=
  ⟨lt_of_lt_of_le tLow_gt h.1, lt_trans wALow_gt h.2.1, h.2.2⟩

lemma sqrt2_bounds : (1.41421 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.41422 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma sqrt6_bounds : (2.44948 : ℝ) < Real.sqrt 6 ∧ Real.sqrt 6 < 2.44949 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `R` is less than `(3426 t + 60 - 120 wA)/17`, i.e. `w̄sep/pool < wA`. -/
lemma Rf_lt (t wA : ℝ) (h : Standing t wA) : 17 * Rf t wA < 3426 * t + 60 - 120 * wA := by
  obtain ⟨ht, hw1, hw2⟩ := std_facts t wA h
  have hR := Rf_nonneg t wA
  have hsq := Rf_sq t wA
  unfold Qf at hsq
  nlinarith [mul_pos (show (0:ℝ) < t by linarith) (show (0:ℝ) < 1 - 2 * wA by linarith),
    mul_pos (show (0:ℝ) < 1 - 2 * wA by linarith) (show (0:ℝ) < 2 * wA by linarith)]

lemma sepPool_lt_wA (t wA : ℝ) (h : Standing t wA) : wSepPool t wA < wA := by
  rw [wSepPool_eq]; have := Rf_lt t wA h; linarith

lemma sep2_lt_sepPool (t wA : ℝ) (h : Standing t wA) : wSep2 t wA < wSepPool t wA := by
  obtain ⟨ht, hw1, hw2⟩ := std_facts t wA h
  have hR := Rf_ge t wA (by linarith)
  obtain ⟨r1, r2⟩ := sqrt2_bounds
  rw [wSepPool_eq]; unfold wSep2
  have hk : (1 + 7 * t - 2 * wA) / (4 * Real.sqrt 2) ≥ (1 + 7 * t - 2 * wA) / (4 * 1.41422) := by
    apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  set k := (1 + 7 * t - 2 * wA) / (4 * Real.sqrt 2)
  have : (1 + 7 * t - 2 * wA) / (4 * 1.41422) = (1 + 7 * t - 2 * wA) * (1 / 5.65688) := by ring
  linarith

lemma sep1_neg (t wA : ℝ) (h : Standing t wA) : wSep1 t wA < 0 := by
  obtain ⟨ht, hw1, hw2⟩ := std_facts t wA h
  unfold wSep1
  have : 1 + 4 * wA - 3 * t < 2 * Real.sqrt (6 * t * (1 + 3 * t - 2 * wA)) := by
    have : 1 + 4 * wA - 3 * t < 2 * 1.2 := by linarith
    have h2 : (1.2:ℝ) ≤ Real.sqrt (6 * t * (1 + 3 * t - 2 * wA)) := by
      have : 0 < 1 + 3 * t - 2 * wA := by linarith
      rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
    linarith
  linarith

lemma N_neg (t wA : ℝ) (h : Standing t wA) :
    36 * wA * (1 - wA) - 32 * wSepPool t wA * (1 - wSepPool t wA)
      - t * (14 + 32 * wSepPool t wA - 60 * wA) - 17 * t ^ 2 - 1 < 0 := by
  obtain ⟨ht, hw1, hw2⟩ := std_facts t wA h
  have h1 := sepPool_lt_wA t wA h
  have h2 : (1620 * wA - 471.4 * t - 60) / 1500 ≤ wSepPool t wA := by
    rw [wSepPool_eq]; have := Rf_ge t wA (by linarith); linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) (sub_nonneg.mpr h2)]

lemma sepPool_lt_bound (t wA : ℝ) (h : Standing t wA) : wSepPool t wA < sepBound t wA := by
  obtain ⟨ht, hw1, hw2⟩ := std_facts t wA h
  obtain ⟨r1, r2⟩ := sqrt6_bounds
  have hR := Rf_nonneg t wA
  have hsq := Rf_sq t wA
  unfold Qf at hsq
  rw [wSepPool_eq]; unfold sepBound
  have key : 17 * Rf t wA < 1500 * ((1 + t) / 2 - 2.44949 * (7 + 10 * t - 14 * wA) / 35)
      - (1620 * wA - 3426 * t - 60) := by
    nlinarith [mul_pos (show (0:ℝ) < t by linarith) (show (0:ℝ) < 1 - 2 * wA by linarith),
      mul_pos (show (0:ℝ) < 1 - 2 * wA by linarith) (show (0:ℝ) < 2 * wA by linarith),
      mul_pos (show (0:ℝ) < t by linarith) (show (0:ℝ) < 1 / 2 - 5 * t / 7 - wA by linarith)]
  nlinarith

end CSAux



namespace CSAux

noncomputable def lf (t wA : ℝ) : ℝ := 1479*t/62500 - 459*wA/50000 + 459/100000
noncomputable def qf (t wA : ℝ) : ℝ := -53*(Real.sqrt 34)*t^2/714 - 233*(Real.sqrt 34)*t*wA/1785 + 22*(Real.sqrt 34)*t/255 - 19*(Real.sqrt 34)*wA^2/510 + (Real.sqrt 34)*wA/15 - 49*(Real.sqrt 34)/2040 - 15256903387*t^2/3748500000 + 88082017*t*wA/26775000 - 72463267*t/53550000 + 815911*wA^2/1530000 - 688411*wA/1530000 + 560911/6120000
noncomputable def Mf (t w1 w2 : ℝ) : ℝ := -65981*(Real.sqrt 34)*t^2/17500000 - 551*(Real.sqrt 34)*t*w1/625000 - 551*(Real.sqrt 34)*t*w2/625000 + 30983*(Real.sqrt 34)*t/17500000 + 171*(Real.sqrt 34)*w1*w2/500000 - 171*(Real.sqrt 34)*w1/1000000 - 171*(Real.sqrt 34)*w2/1000000 + 171*(Real.sqrt 34)/2000000 + 148778260733*t^2/3675000000000 + 23661419*t*w1/1875000000 + 23661419*t*w2/1875000000 - 29887213*t/3750000000 - 2447733*w1*w2/500000000 + 2447733*w1/1000000000 + 2447733*w2/1000000000 - 2447733/2000000000

lemma phi_eq (t wA : ℝ) : profitSep4 t wA (wSepPool t wA) - profitPool t wA (wIBar t wA)
    = lf t wA * Rf t wA + qf t wA := by
  have hR := Rf_sq t wA
  have hs : Real.sqrt 34 ^ 2 = 34 := Real.sq_sqrt (by norm_num)
  rw [wSepPool_eq]
  unfold Qf at hR
  simp only [profitSep4, profitPool, stateProfitVI, sepQO1H, sepQIH, poolQO1, poolQO2H, poolQI,
    wIBar, lf, qf]
  linear_combination (-289/6000000 : ℝ) * hR + (767*t^2/56644 + 767*t*wA/20230 - 767*t/40460
    + 767*wA^2/28900 - 767*wA/28900 + 767/115600) * hs

lemma cross_eq (t w1 w2 : ℝ) : qf t w2 * lf t w1 - qf t w1 * lf t w2 = (w2 - w1) * Mf t w1 w2 := by
  unfold qf lf Mf; ring

lemma Mf_pos (t w1 w2 : ℝ) (ht : 0.28 ≤ t) (ht2 : t ≤ 0.6931) (h1 : 0.004965 ≤ w1) (h12 : w1 ≤ w2)
    (h2 : w2 ≤ 1 / 2 - 5 * t / 7) : 0 < Mf t w1 w2 := by
  obtain ⟨s1, s2⟩ := sqrt34_fine
  unfold Mf
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h12), mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr h2),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht2),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ht), mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr ht)]

lemma qf_neg (t wA : ℝ) (ht : 0.28 ≤ t) (h1 : 0.004965 ≤ wA) (h2 : wA ≤ 1 / 2 - 5 * t / 7) :
    qf t wA < 0 := by
  obtain ⟨s1, s2⟩ := sqrt34_fine
  unfold qf
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr h2),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ht)]

lemma lf_pos (t wA : ℝ) (ht : 0.28 ≤ t) (h2 : wA ≤ 1 / 2 - 5 * t / 7) : 0 < lf t wA := by
  unfold lf; nlinarith

end CSAux



namespace CSAux

set_option maxHeartbeats 4000000

/-- F10: `Πs,4_I(0) < Πp_I(w̄I)` for `t ≤ 0.401`. -/
lemma f10 (t wA : ℝ) (ht : 0.28 ≤ t) (ht2 : t ≤ 0.401) (h1 : 0.004965 ≤ wA)
    (h2 : wA ≤ 1 / 2 - 5 * t / 7) : profitSep4 t wA 0 < profitPool t wA (wIBar t wA) := by
  obtain ⟨s1, s2⟩ := sqrt34_fine
  have hs : Real.sqrt 34 ^ 2 = 34 := Real.sq_sqrt (by norm_num)
  have key : profitPool t wA (wIBar t wA) - profitSep4 t wA 0 =
      53*(Real.sqrt 34)*t^2/714 + 233*(Real.sqrt 34)*t*wA/1785 - 22*(Real.sqrt 34)*t/255
      + 19*(Real.sqrt 34)*wA^2/510 - (Real.sqrt 34)*wA/15 + 49*(Real.sqrt 34)/2040 - 59389*t^2/119952
      - 52249*t*wA/42840 + 10831*t/21420 - 30587*wA^2/30600 + 28037*wA/30600 - 3503/30600 := by
    simp only [profitSep4, profitPool, stateProfitVI, sepQO1H, sepQIH, poolQO1, poolQO2H, poolQI, wIBar]
    linear_combination (-767*t^2/56644 - 767*t*wA/20230 + 767*t/40460 - 767*wA^2/28900
      + 767*wA/28900 - 767/115600) * hs
  have : 0 < 53*(Real.sqrt 34)*t^2/714 + 233*(Real.sqrt 34)*t*wA/1785 - 22*(Real.sqrt 34)*t/255
      + 19*(Real.sqrt 34)*wA^2/510 - (Real.sqrt 34)*wA/15 + 49*(Real.sqrt 34)/2040 - 59389*t^2/119952
      - 52249*t*wA/42840 + 10831*t/21420 - 30587*wA^2/30600 + 28037*wA/30600 - 3503/30600 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr h2),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ht), mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht2),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ht2), mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr ht2)]
  linarith

/-- F8: at `wA = 0.01`, `w̄sep/pool < 0`. -/
lemma f8 (t : ℝ) (ht : 0.28 ≤ t) : wSepPool t 0.01 < 0 := by
  rw [wSepPool_eq]
  have hR := Rf_nonneg t 0.01
  have hsq := Rf_sq t 0.01
  unfold Qf at hsq
  have : 17 * Rf t 0.01 < 3426 * t + 43.8 := by nlinarith
  linarith

/-- `Πs,4_I` is a concave quadratic increasing for `w ≤ (1+t)/2`. -/
lemma sep4_diff (t wA w v : ℝ) : profitSep4 t wA w - profitSep4 t wA v = 3 / 8 * (w - v) * ((1 + t) - w - v) := by
  simp only [profitSep4, stateProfitVI, sepQO1H, sepQIH]; ring

lemma sep4_lt (t wA w v : ℝ) (h : v < w) (hw : w ≤ (1 + t) / 2) : profitSep4 t wA v < profitSep4 t wA w := by
  have := sep4_diff t wA w v
  nlinarith [mul_pos (sub_pos.mpr h) (show (0:ℝ) < (1 + t) - w - v by linarith)]

noncomputable def phif (t wA : ℝ) : ℝ := lf t wA * Rf t wA + qf t wA

lemma phif_eq (t wA : ℝ) : phif t wA = profitSep4 t wA (wSepPool t wA) - profitPool t wA (wIBar t wA) :=
  (phi_eq t wA).symm

lemma phif_cont (t : ℝ) : Continuous (phif t) := by
  unfold phif lf qf Rf Qf; fun_prop

lemma Qf_mono (t w1 w2 : ℝ) (ht : 0.28 ≤ t) (h1 : 0 ≤ w1) (h12 : w1 ≤ w2) (h2 : w2 ≤ 1 / 2) :
    Qf t w1 ≤ Qf t w2 := by
  unfold Qf; nlinarith [mul_nonneg (sub_nonneg.mpr h12) (show (0:ℝ) ≤ 320 * t - 25 * (2 - 2 * w1 - 2 * w2) by nlinarith)]

lemma phif_thresh (t w1 w2 : ℝ) (ht : 0.28 ≤ t) (ht2 : t ≤ 0.6931) (h1 : 0.004965 ≤ w1) (h12 : w1 < w2)
    (h2 : w2 ≤ 1 / 2 - 5 * t / 7) (hp : 0 ≤ phif t w1) : 0 < phif t w2 := by
  have hl1 := lf_pos t w1 ht (by linarith)
  have hl2 := lf_pos t w2 ht h2
  have hq1 := qf_neg t w1 ht h1 (by linarith)
  have hM := Mf_pos t w1 w2 ht ht2 h1 h12.le h2
  have hc := cross_eq t w1 w2
  have hR : Rf t w1 ≤ Rf t w2 := Real.sqrt_le_sqrt (Qf_mono t w1 w2 ht (by linarith) h12.le (by linarith))
  have hR1 := Rf_nonneg t w1
  unfold phif at hp ⊢
  have hcross : qf t w1 * lf t w2 < qf t w2 * lf t w1 := by nlinarith [mul_pos (sub_pos.mpr h12) hM]
  have : 0 < lf t w1 * (lf t w2 * Rf t w2 + qf t w2) := by
    nlinarith [mul_le_mul_of_nonneg_left hR (mul_pos hl1 hl2).le, mul_nonneg hl2.le hp]
  exact pos_of_mul_pos_right this hl1.le

end CSAux



namespace CSAux

set_option maxHeartbeats 4000000

noncomputable def Dp (t wA : ℝ) : ℝ := -848*(Real.sqrt 34)*t^2/1071 - 7456*(Real.sqrt 34)*t*wA/5355
  + 704*(Real.sqrt 34)*t/765 - 304*(Real.sqrt 34)*wA^2/765 + 32*(Real.sqrt 34)*wA/45 - 196*(Real.sqrt 34)/765
  + 141269*t^2/22491 + 208996*t*wA/16065 - 54518*t/16065 + 122348*wA^2/11475 - 112148*wA/11475 + 25487/11475

lemma D_eq (t wA : ℝ) : (1 + t) ^ 2 - 32 / 3 * (profitPool t wA (wIBar t wA)
    - ((1 + t) ^ 2 + (1 - t + 2 * wA) ^ 2) / 32) = Dp t wA := by
  have hs : Real.sqrt 34 ^ 2 = 34 := Real.sq_sqrt (by norm_num)
  simp only [profitPool, stateProfitVI, poolQO1, poolQO2H, poolQI, wIBar, Dp]
  linear_combination (6136*t^2/42483 + 12272*t*wA/30345 - 6136*t/30345 + 6136*wA^2/21675
    - 6136*wA/21675 + 1534/21675) * hs

lemma wEqualBar_eq (t wA : ℝ) : wEqualBar t wA = ((1 + t) - Real.sqrt (Dp t wA)) / 2 := by
  unfold wEqualBar; rw [D_eq]

lemma Dp_ge (t wA : ℝ) (ht : 35 / 92 ≤ t) (h1 : 0.004965 ≤ wA) (h2 : wA ≤ 1 / 2 - 5 * t / 7) :
    1.2 ≤ Dp t wA := by
  obtain ⟨s1, s2⟩ := sqrt34_fine
  unfold Dp
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr h2),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ht), mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h2),
    mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht), mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h1)]

lemma Dp_diff (t w1 w2 : ℝ) (ht : 35 / 92 ≤ t) (h1 : 0.004965 ≤ w1) (h12 : w1 ≤ w2)
    (h2 : w2 ≤ 1 / 2 - 5 * t / 7) : Dp t w1 - Dp t w2 ≤ 3.8 * (w2 - w1) := by
  obtain ⟨s1, s2⟩ := sqrt34_fine
  have e : Dp t w1 - Dp t w2 = (w2 - w1) * (-( -7456*(Real.sqrt 34)*t/5355 + 32*(Real.sqrt 34)/45
      + 208996*t/16065 - 112148/11475) - (-304*(Real.sqrt 34)/765 + 122348/11475) * (w1 + w2)) := by
    unfold Dp; ring
  rw [e, mul_comm (3.8:ℝ)]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ht), mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr ht)]

lemma gap_mono_proof (t : ℝ) (ht : 35 / 92 < t) :
    StrictMonoOn (fun wA : ℝ => wSepPool t wA - wEqualBar t wA) (Set.Ioo wALow (1 / 2 - 5 * t / 7)) := by
  have hl := wALow_gt
  intro w1 hw1 w2 hw2 h12
  simp only [Set.mem_Ioo] at hw1 hw2
  simp only
  rw [wEqualBar_eq, wEqualBar_eq, wSepPool_eq, wSepPool_eq]
  have hR : Rf t w1 ≤ Rf t w2 :=
    Real.sqrt_le_sqrt (Qf_mono t w1 w2 (by linarith) (by linarith) h12.le (by linarith))
  have hD1 := Dp_ge t w1 ht.le (by linarith) hw1.2.le
  have hD2 := Dp_ge t w2 ht.le (by linarith) hw2.2.le
  have hdd := Dp_diff t w1 w2 ht.le (by linarith) h12.le hw2.2.le
  have hs1 : Real.sqrt 1.2 ≤ Real.sqrt (Dp t w1) := Real.sqrt_le_sqrt hD1
  have hs2 : Real.sqrt 1.2 ≤ Real.sqrt (Dp t w2) := Real.sqrt_le_sqrt hD2
  have h12' : (1.09 : ℝ) ≤ Real.sqrt 1.2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hq1 := Real.sq_sqrt (show 0 ≤ Dp t w1 by linarith)
  have hq2 := Real.sq_sqrt (show 0 ≤ Dp t w2 by linarith)
  -- √D1 − √D2 ≤ 3.8 (w2 − w1) / 2.18
  have key : (Real.sqrt (Dp t w1) - Real.sqrt (Dp t w2)) * (Real.sqrt (Dp t w1) + Real.sqrt (Dp t w2))
      = Dp t w1 - Dp t w2 := by nlinarith
  have hsum : 2.18 ≤ Real.sqrt (Dp t w1) + Real.sqrt (Dp t w2) := by linarith
  have hdiff : Real.sqrt (Dp t w1) - Real.sqrt (Dp t w2) ≤ 1.75 * (w2 - w1) := by
    by_contra hc; rw [not_le] at hc
    have : 1.75 * (w2 - w1) * 2.18 < (Real.sqrt (Dp t w1) - Real.sqrt (Dp t w2)) * (Real.sqrt (Dp t w1) + Real.sqrt (Dp t w2)) := by
      have hpos : 0 < 1.75 * (w2 - w1) := by linarith
      nlinarith
    linarith
  linarith

end CSAux

theorem solution (t : ℝ) (ht : 35 / 92 < t) :
    StrictMonoOn (fun wA : ℝ => CoopetSourcing.WholesalePrice.wSepPool t wA -
      CoopetSourcing.WholesalePrice.wEqualBar t wA) (Set.Ioo CoopetSourcing.WholesalePrice.wALow (1 / 2 - 5 * t / 7)) :=
  CSAux.gap_mono_proof t ht

