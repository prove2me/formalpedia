-- Prove2me | solution 1 for CoopetSourcing.WholesalePrice.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:22:47.883301+00:00
-- url     : https://prove2.me/submissions/f98182b4-500b-42e3-afc6-371fd84703be

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model
import Theorems.Thm_CoopetSourcing_WholesalePrice_lemma_4

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

lemma f6_A_lo (t e : ℝ) (g1 : 0 ≤ t - 7/25) (g2 : 0 ≤ e) (g3 : 0 ≤ ((1275000000/11802018251 - 23460000000*t/82614127757)) - e) :
    0 < (-2022041180689*e^4/21178404000000 - 2234923682539*e^3*t/1235406900000 - 2805066847*e^3/35297340000 - 3150220569337847*e^2*t^2/345913932000000 - 250564519683*e^2*t/823604600000 - 24057463*e^2/1411893600 - 2942367570868069*e*t^3/201783127000000 + 2024474670763*e*t^2/28826161000000 + 138940987*e*t/8236046000 - 7975*e/4706312 - 169201184032565257*t^4/22599710224000000 + 1376989289437173*t^3/403566254000000 - 3183947687*t^2/18016350625 + 295275*t/65888368 - 625/9412624) := by
  linarith [g3, (mul_nonneg g3 g3), (mul_nonneg (mul_nonneg g3 g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g3 g3) g3) g3), g2, (mul_nonneg g2 g3), (mul_nonneg (mul_nonneg g2 g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g2 g3) g3) g3), (mul_nonneg g2 g2), (mul_nonneg (mul_nonneg g2 g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g3) g3), (mul_nonneg (mul_nonneg g2 g2) g2), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g2) g2), g1, (mul_nonneg g1 g3), (mul_nonneg (mul_nonneg g1 g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g3) g3) g3), (mul_nonneg g1 g2), (mul_nonneg (mul_nonneg g1 g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g3) g3), (mul_nonneg (mul_nonneg g1 g2) g2), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g2) g2), (mul_nonneg g1 g1), (mul_nonneg (mul_nonneg g1 g1) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g3) g3), (mul_nonneg (mul_nonneg g1 g1) g2), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g2) g2), (mul_nonneg (mul_nonneg g1 g1) g1), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g2), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g1)]

lemma f6_A_hi (t e : ℝ) (g1 : 0 ≤ t - 7/25) (g2 : 0 ≤ e) (g3 : 0 ≤ ((1275000000/11802018251 - 23460000000*t/82614127757)) - e) :
    0 < (-2022041180689*e^4/21178404000000 - 2234923682539*e^3*t/1235406900000 - 2805066847*e^3/35297340000 - 3150220569337847*e^2*t^2/345913932000000 - 250564519683*e^2*t/823604600000 - 24057463*e^2/1411893600 - 2942367570868069*e*t^3/201783127000000 + 2024474670763*e*t^2/28826161000000 + 138940987*e*t/8236046000 - 7975*e/4706312 - 169201184032565257*t^4/22599710224000000 + 1376989289437173*t^3/403566254000000 - 3183947687*t^2/18016350625 + 295275*t/65888368 - 625/9412624) := by
  linarith [g3, (mul_nonneg g3 g3), (mul_nonneg (mul_nonneg g3 g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g3 g3) g3) g3), g2, (mul_nonneg g2 g3), (mul_nonneg (mul_nonneg g2 g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g2 g3) g3) g3), (mul_nonneg g2 g2), (mul_nonneg (mul_nonneg g2 g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g3) g3), (mul_nonneg (mul_nonneg g2 g2) g2), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g2) g2), g1, (mul_nonneg g1 g3), (mul_nonneg (mul_nonneg g1 g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g3) g3) g3), (mul_nonneg g1 g2), (mul_nonneg (mul_nonneg g1 g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g3) g3), (mul_nonneg (mul_nonneg g1 g2) g2), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g2) g2), (mul_nonneg g1 g1), (mul_nonneg (mul_nonneg g1 g1) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g3) g3), (mul_nonneg (mul_nonneg g1 g1) g2), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g2) g2), (mul_nonneg (mul_nonneg g1 g1) g1), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g2), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g1)]

lemma f6_psi (t e s : ℝ) (s1 : (5830951/1000000) ≤ s) (s2 : s ≤ (728869/125000)) (g1 : 0 ≤ t - 7/25) (g2 : 0 ≤ e)
    (g3 : 0 ≤ ((1275000000/11802018251 - 23460000000*t/82614127757)) - e) : 0 < (-2022041180689*e^4/21178404000000 - 2234923682539*e^3*t/1235406900000 - 2805066847*e^3/35297340000 - 3150220569337847*e^2*t^2/345913932000000 - 250564519683*e^2*t/823604600000 - 24057463*e^2/1411893600 - 2942367570868069*e*t^3/201783127000000 + 2024474670763*e*t^2/28826161000000 + 138940987*e*t/8236046000 - 7975*e/4706312 - 169201184032565257*t^4/22599710224000000 + 1376989289437173*t^3/403566254000000 - 3183947687*t^2/18016350625 + 295275*t/65888368 - 625/9412624) + s * ((0)) := by
  have h1 := f6_A_lo t e g1 g2 g3
  have h2 := f6_A_hi t e g1 g2 g3
  have key : ((-2022041180689*e^4/21178404000000 - 2234923682539*e^3*t/1235406900000 - 2805066847*e^3/35297340000 - 3150220569337847*e^2*t^2/345913932000000 - 250564519683*e^2*t/823604600000 - 24057463*e^2/1411893600 - 2942367570868069*e*t^3/201783127000000 + 2024474670763*e*t^2/28826161000000 + 138940987*e*t/8236046000 - 7975*e/4706312 - 169201184032565257*t^4/22599710224000000 + 1376989289437173*t^3/403566254000000 - 3183947687*t^2/18016350625 + 295275*t/65888368 - 625/9412624) + s * ((0))) * ((1/1000000)) =
      ((728869/125000) - s) * ((-2022041180689*e^4/21178404000000 - 2234923682539*e^3*t/1235406900000 - 2805066847*e^3/35297340000 - 3150220569337847*e^2*t^2/345913932000000 - 250564519683*e^2*t/823604600000 - 24057463*e^2/1411893600 - 2942367570868069*e*t^3/201783127000000 + 2024474670763*e*t^2/28826161000000 + 138940987*e*t/8236046000 - 7975*e/4706312 - 169201184032565257*t^4/22599710224000000 + 1376989289437173*t^3/403566254000000 - 3183947687*t^2/18016350625 + 295275*t/65888368 - 625/9412624)) + (s - (5830951/1000000)) * ((-2022041180689*e^4/21178404000000 - 2234923682539*e^3*t/1235406900000 - 2805066847*e^3/35297340000 - 3150220569337847*e^2*t^2/345913932000000 - 250564519683*e^2*t/823604600000 - 24057463*e^2/1411893600 - 2942367570868069*e*t^3/201783127000000 + 2024474670763*e*t^2/28826161000000 + 138940987*e*t/8236046000 - 7975*e/4706312 - 169201184032565257*t^4/22599710224000000 + 1376989289437173*t^3/403566254000000 - 3183947687*t^2/18016350625 + 295275*t/65888368 - 625/9412624)) := by ring
  have hpos : 0 < ((-2022041180689*e^4/21178404000000 - 2234923682539*e^3*t/1235406900000 - 2805066847*e^3/35297340000 - 3150220569337847*e^2*t^2/345913932000000 - 250564519683*e^2*t/823604600000 - 24057463*e^2/1411893600 - 2942367570868069*e*t^3/201783127000000 + 2024474670763*e*t^2/28826161000000 + 138940987*e*t/8236046000 - 7975*e/4706312 - 169201184032565257*t^4/22599710224000000 + 1376989289437173*t^3/403566254000000 - 3183947687*t^2/18016350625 + 295275*t/65888368 - 625/9412624) + s * ((0))) * ((1/1000000)) := by
    rw [key]
    rcases eq_or_lt_of_le s1 with h | h
    · subst h; nlinarith
    · nlinarith [mul_nonneg (sub_nonneg.mpr s2) h1.le]
  exact pos_of_mul_pos_left hpos (by norm_num)

/-- F6: when the unconstrained pooling optimum `w°` lies below `w̄I`, the separating profit at
`w̄sep/pool` strictly exceeds `Πp_I(w°)`. -/
lemma f6 (t wA : ℝ) (h : Standing t wA)
    (hw0 : (3703 - 4066 * t - 242 * wA) / 9204 ≤ wIBar t wA) :
    profitPool t wA ((3703 - 4066 * t - 242 * wA) / 9204) < profitSep4 t wA (wSepPool t wA) := by
  obtain ⟨ht, hw1, hw2⟩ := std_facts t wA h
  obtain ⟨s1, s2⟩ := sqrt34_fine
  set s := Real.sqrt 34 with hsdef
  have hs : s ^ 2 = 34 := Real.sq_sqrt (by norm_num)
  set e := 1 / 2 - 5 * t / 7 - wA with hedef
  have he : 0 ≤ e := by linarith
  have hwA : wA = 1 / 2 - 5 * t / 7 - e := by rw [hedef]; ring
  -- d = w̄I − w°
  have hd : 0 ≤ -e*s/5 + 323*e/2301 - 1564*t/5369 + 85/767 := by
    have : wIBar t wA - (3703 - 4066 * t - 242 * wA) / 9204 = -e*s/5 + 323*e/2301 - 1564*t/5369 + 85/767 := by
      unfold wIBar; rw [hwA]; ring
    linarith
  have g3 : 0 ≤ ((1275000000/11802018251 - 23460000000*t/82614127757)) - e := by
    have hc : (11802018251/11505000000) ≤ s / 5 - 323 / 2301 := by linarith
    have : e * (s / 5 - 323 / 2301) ≤ 85/767 - 1564*t/5369 := by linarith
    have hn : 0 ≤ 85/767 - 1564*t/5369 := by nlinarith
    have : e * (11802018251/11505000000) ≤ 85/767 - 1564*t/5369 := by nlinarith
    have : e ≤ (85/767 - 1564*t/5369) / (11802018251/11505000000) := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have hpsi := f6_psi t e s (by linarith) (by linarith) (by linarith) he g3
  -- the profit identities
  have hphi := phi_eq t wA
  have hq := qf_neg t wA (by linarith) (by linarith) (by linarith)
  have hl := lf_pos t wA (by linarith) (by linarith)
  have hR := Rf_nonneg t wA
  have hRsq := Rf_sq t wA
  set w0 := (3703 - 4066 * t - 242 * wA) / 9204 with hw0def
  have hpool : profitPool t wA w0 - profitPool t wA (wIBar t wA) = 767 / 1156 * (w0 - wIBar t wA) ^ 2 := by
    rw [hw0def]; simp only [profitPool, stateProfitVI, poolQO1, poolQO2H, poolQI]; ring
  set T := -(qf t wA - 767 / 1156 * (w0 - wIBar t wA) ^ 2) with hT
  have hTpos : 0 < T := by rw [hT]; nlinarith [sq_nonneg (w0 - wIBar t wA)]
  have hid : lf t wA ^ 2 * Qf t wA - T ^ 2 = (-2022041180689*e^4/21178404000000 - 2234923682539*e^3*t/1235406900000 - 2805066847*e^3/35297340000 - 3150220569337847*e^2*t^2/345913932000000 - 250564519683*e^2*t/823604600000 - 24057463*e^2/1411893600 - 2942367570868069*e*t^3/201783127000000 + 2024474670763*e*t^2/28826161000000 + 138940987*e*t/8236046000 - 7975*e/4706312 - 169201184032565257*t^4/22599710224000000 + 1376989289437173*t^3/403566254000000 - 3183947687*t^2/18016350625 + 295275*t/65888368 - 625/9412624) + s * ((0)) := by
    rw [hT, hw0def]; unfold lf qf Qf wIBar; rw [← hsdef, hwA]
    linear_combination ((-588289*e^4*s^2/835210000 + 27000379*e^4/7369500000 - 166011319*e^3*t/1264375000 - 319*e^3/57800 - 116585326343*e^2*t^2/354025000000 + 11811*e^2*t/809200 - e^2/2312)) * hs
  have hlr : T < lf t wA * Rf t wA := by
    have h1 : T ^ 2 < (lf t wA * Rf t wA) ^ 2 := by rw [mul_pow, hRsq]; linarith
    have h2 : 0 ≤ lf t wA * Rf t wA := mul_nonneg hl.le hR
    nlinarith
  linarith

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


lemma gap_cont (t : ℝ) : Continuous (fun wA : ℝ => wSepPool t wA - wEqualBar t wA) := by
  unfold wSepPool wEqualBar profitPool wIBar
  simp only [stateProfitVI, poolQO2H, poolQI, poolQO1]
  fun_prop

lemma gap_top (t : ℝ) (ht : 0 < t) :
    wSepPool t (1 / 2 - 5 * t / 7) - wEqualBar t (1 / 2 - 5 * t / 7) =
      (153 * (Real.sqrt 5134 - 122) * t + 125 * Real.sqrt (21 * t * (51 * t + 52))) / 5250 := by
  have h1 : Real.sqrt (6 * (25 * (1 - 2 * (1 / 2 - 5 * t / 7)) ^ 2 + 6064 * t ^ 2
      - 320 * t * (1 - 2 * (1 / 2 - 5 * t / 7)))) = 18 * Real.sqrt 5134 * t / 7 := by
    have hnn : 0 ≤ 18 * Real.sqrt 5134 * t / 7 := by positivity
    rw [← Real.sqrt_sq hnn]; congr 1
    have := Real.sq_sqrt (show (0:ℝ) ≤ 5134 by norm_num)
    linear_combination (-(324 : ℝ) * t ^ 2 / 49) * this
  have hX : 0 ≤ 21 * t * (51 * t + 52) := by positivity
  have h2 : Real.sqrt ((1 + t) ^ 2 - 32 / 3 * (profitPool t (1 / 2 - 5 * t / 7)
      (wIBar t (1 / 2 - 5 * t / 7)) - ((1 + t) ^ 2 + (1 - t + 2 * (1 / 2 - 5 * t / 7)) ^ 2) / 32))
      = Real.sqrt (21 * t * (51 * t + 52)) / 21 := by
    have hnn : 0 ≤ Real.sqrt (21 * t * (51 * t + 52)) / 21 := by positivity
    rw [← Real.sqrt_sq hnn]; congr 1
    have := Real.sq_sqrt hX
    simp only [profitPool, stateProfitVI, poolQO1, poolQO2H, poolQI, wIBar]
    linear_combination (-(1 : ℝ) / 441) * this
  unfold wSepPool wEqualBar
  rw [h1, h2]
  ring

lemma sqrt5134_bounds : (71.65 : ℝ) < Real.sqrt 5134 ∧ Real.sqrt 5134 < 71.66 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- With `k = 153(122 - √5134)` and `A = k²/15625 − 1071`, a positive `x` makes the
expression of (7) positive iff `A x < 1092`. -/
lemma eq7_expr_pos_iff (x : ℝ) (hx : 0 < x) :
    0 < 153 * (Real.sqrt 5134 - 122) * x + 125 * Real.sqrt (21 * x * (51 * x + 52)) ↔
      ((153 * (122 - Real.sqrt 5134)) ^ 2 / 15625 - 1071) * x < 1092 := by
  obtain ⟨r1, r2⟩ := sqrt5134_bounds
  set k := 153 * (122 - Real.sqrt 5134) with hk
  have hk0 : 0 ≤ k * x / 125 := by apply div_nonneg _ (by norm_num); apply mul_nonneg _ hx.le; linarith
  have e : 153 * (Real.sqrt 5134 - 122) * x + 125 * Real.sqrt (21 * x * (51 * x + 52)) =
      125 * (Real.sqrt (21 * x * (51 * x + 52)) - k * x / 125) := by rw [hk]; ring
  rw [e]
  constructor
  · intro h
    have h' : k * x / 125 < Real.sqrt (21 * x * (51 * x + 52)) := by linarith
    rw [Real.lt_sqrt hk0] at h'
    have : x * ((k ^ 2 / 15625 - 1071) * x - 1092) < 0 := by nlinarith
    have := (mul_neg_iff.mp this)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  · intro h
    have h' : k * x / 125 < Real.sqrt (21 * x * (51 * x + 52)) := by
      rw [Real.lt_sqrt hk0]
      have : x * ((k ^ 2 / 15625 - 1071) * x - 1092) < 0 := mul_neg_of_pos_of_neg hx (by linarith)
      nlinarith
    linarith

lemma eq7_root (tbar : ℝ) (htbar : tbar ≠ 0) (h7 : Eq7 tbar) :
    0 < tbar ∧ ((153 * (122 - Real.sqrt 5134)) ^ 2 / 15625 - 1071) * tbar = 1092 := by
  obtain ⟨r1, r2⟩ := sqrt5134_bounds
  unfold Eq7 at h7
  set k := 153 * (122 - Real.sqrt 5134) with hk
  have hs : Real.sqrt (21 * tbar * (51 * tbar + 52)) = k * tbar / 125 := by
    rw [hk]; linarith
  have hpos : 0 < tbar := by
    have h0 := Real.sqrt_nonneg (21 * tbar * (51 * tbar + 52))
    rw [hs] at h0
    have hkpos : 0 < k := by rw [hk]; nlinarith
    rcases lt_or_gt_of_ne htbar with h | h
    · nlinarith
    · exact h
  refine ⟨hpos, ?_⟩
  have hX : 0 ≤ 21 * tbar * (51 * tbar + 52) := by positivity
  have := Real.sq_sqrt hX
  rw [hs] at this
  have : tbar * ((k ^ 2 / 15625 - 1071) * tbar - 1092) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h htbar
  · linarith


lemma sep4_at_wEqualBar (t wA : ℝ)
    (hD : 0 ≤ (1 + t) ^ 2 - 32 / 3 * (profitPool t wA (wIBar t wA) - ((1 + t) ^ 2 + (1 - t + 2 * wA) ^ 2) / 32)) :
    profitSep4 t wA (wEqualBar t wA) = profitPool t wA (wIBar t wA) := by
  have hsq := Real.sq_sqrt hD
  unfold wEqualBar
  set D := (1 + t) ^ 2 - 32 / 3 * (profitPool t wA (wIBar t wA) - ((1 + t) ^ 2 + (1 - t + 2 * wA) ^ 2) / 32) with hDdef
  set P := profitPool t wA (wIBar t wA)
  simp only [profitSep4, stateProfitVI, sepQO1H, sepQIH]
  have : P = ((1 + t) ^ 2 + (1 - t + 2 * wA) ^ 2) / 32 + 3 / 32 * ((1 + t) ^ 2 - D) := by rw [hDdef]; ring
  rw [this]
  linear_combination (-3 / 32 : ℝ) * hsq

lemma phif_top_pos_iff (tbar : ℝ) (htbar : tbar ≠ 0) (h7 : Eq7 tbar) (t : ℝ) (ht : 0.28 ≤ t) :
    0 < phif t (1 / 2 - 5 * t / 7) ↔ t < tbar := by
  have htp : 0 < t := by linarith
  set wT := 1 / 2 - 5 * t / 7 with hwT
  -- the discriminant at the top
  have hD : (1 + t) ^ 2 - 32 / 3 * (profitPool t wT (wIBar t wT) - ((1 + t) ^ 2 + (1 - t + 2 * wT) ^ 2) / 32)
      = t * (51 * t + 52) / 21 := by
    rw [hwT]; simp only [profitPool, stateProfitVI, poolQO1, poolQO2H, poolQI, wIBar]; ring
  have hDnn : 0 ≤ (1 + t) ^ 2 - 32 / 3 * (profitPool t wT (wIBar t wT) - ((1 + t) ^ 2 + (1 - t + 2 * wT) ^ 2) / 32) := by
    rw [hD]; positivity
  have heq := sep4_at_wEqualBar t wT hDnn
  have hgap := gap_top t htp
  rw [← hwT] at hgap
  -- a_top ≤ (1+t)/2
  have h1 : Real.sqrt (6 * (25 * (1 - 2 * wT) ^ 2 + 6064 * t ^ 2 - 320 * t * (1 - 2 * wT)))
      = 18 * Real.sqrt 5134 * t / 7 := by
    have hnn : 0 ≤ 18 * Real.sqrt 5134 * t / 7 := by positivity
    rw [← Real.sqrt_sq hnn]; congr 1
    have := Real.sq_sqrt (show (0:ℝ) ≤ 5134 by norm_num)
    rw [hwT]; linear_combination (-(324 : ℝ) * t ^ 2 / 49) * this
  obtain ⟨r1, r2⟩ := sqrt5134_bounds
  have ha : wSepPool t wT < (1 + t) / 2 := by
    unfold wSepPool; rw [h1, hwT]; nlinarith
  have he : wEqualBar t wT ≤ (1 + t) / 2 := by
    unfold wEqualBar; have := Real.sqrt_nonneg ((1 + t) ^ 2 - 32 / 3 * (profitPool t wT (wIBar t wT)
      - ((1 + t) ^ 2 + (1 - t + 2 * wT) ^ 2) / 32)); linarith
  have hphi : phif t wT = 3 / 8 * (wSepPool t wT - wEqualBar t wT) * ((1 + t) - wSepPool t wT - wEqualBar t wT) := by
    rw [phif_eq, ← heq, sep4_diff]
  have hfac : 0 < (1 + t) - wSepPool t wT - wEqualBar t wT := by
    rcases eq_or_lt_of_le he with h | h
    · -- wEqualBar = (1+t)/2 means the root is the vertex
      linarith
    · linarith
  have hiff : 0 < phif t wT ↔ 0 < wSepPool t wT - wEqualBar t wT := by
    rw [hphi]; constructor
    · intro h; by_contra h'; rw [not_lt] at h'; nlinarith
    · intro h; positivity
  rw [hiff, hgap]
  obtain ⟨hb0, hb⟩ := eq7_root tbar htbar h7
  have hA : 0 < (153 * (122 - Real.sqrt 5134)) ^ 2 / 15625 - 1071 := by nlinarith
  rw [div_pos_iff_of_pos_right (by norm_num), eq7_expr_pos_iff t htp]
  constructor
  · intro h; by_contra h'; rw [not_lt] at h'; nlinarith
  · intro h; nlinarith

end CSAux



namespace CSAux

lemma wALow_lt : wALow < 0.01 := by
  unfold wALow
  obtain ⟨h1, h2⟩ := sqrt34_fine
  rw [div_lt_iff_of_neg (by nlinarith)]; nlinarith

lemma tbar_lt (tbar : ℝ) (htbar : tbar ≠ 0) (h7 : Eq7 tbar) : tbar < 0.401 := by
  obtain ⟨hb0, hb⟩ := eq7_root tbar htbar h7
  obtain ⟨r1, r2⟩ := sqrt5134_bounds
  have hk : 7702 < 153 * (122 - Real.sqrt 5134) := by linarith
  have hk2 : 7702 ^ 2 < (153 * (122 - Real.sqrt 5134)) ^ 2 := by
    have := pow_lt_pow_left₀ hk (by norm_num) (two_ne_zero); simpa using this
  have hA : 2725 < (153 * (122 - Real.sqrt 5134)) ^ 2 / 15625 - 1071 := by
    rw [show (2725:ℝ) = (2725 + 1071) - 1071 by norm_num]
    have : (2725 + 1071 : ℝ) < (153 * (122 - Real.sqrt 5134)) ^ 2 / 15625 := by
      rw [lt_div_iff₀ (by norm_num)]; nlinarith
    linarith
  nlinarith

lemma t_lt_of_std (t wA : ℝ) (h : Standing t wA) : t ≤ 0.6931 := by
  obtain ⟨ht, hw1, hw2⟩ := std_facts t wA h; linarith

/-- At `w̄sep/pool ≥ 0` the separating profit is on its fourth piece (`Q̂O,1(·|L) = 0`). -/
lemma sep_at_pool (t wA : ℝ) (h : Standing t wA) (ha : 0 ≤ wSepPool t wA) :
    profitSep t wA (wSepPool t wA) = profitSep4 t wA (wSepPool t wA) := by
  have h1 := sep1_neg t wA h
  have h2 := sep2_lt_sepPool t wA h
  have h3 := N_neg t wA h
  have h4 := sepPool_lt_wA t wA h
  have hx : max 0 ((36 * wA * (1 - wA) - 32 * wSepPool t wA * (1 - wSepPool t wA)
      - t * (14 + 32 * wSepPool t wA - 60 * wA) - 17 * t ^ 2 - 1) / (64 * (wA - wSepPool t wA))) = 0 := by
    apply max_eq_left
    apply div_nonpos_of_nonpos_of_nonneg h3.le; linarith
  have hQ1 : sepQO1L t wA (wSepPool t wA) = 0 := by
    unfold sepQO1L
    rw [if_neg (by linarith), if_neg (by linarith), hx]
  have hQ2 : sepQO2L t wA (wSepPool t wA) = (1 - t - 2 * wA) / 2 := by
    unfold sepQO2L; rw [if_neg (by linarith), hQ1]; ring
  have hQI : sepQIL t wA (wSepPool t wA) = (1 - t + 2 * wA) / 4 := by
    unfold sepQIL; rw [if_neg (by linarith)]
  unfold profitSep profitSep4
  rw [hQ1, hQ2, hQI]

lemma pool_vertex (t wA w : ℝ) : profitPool t wA w = profitPool t wA ((3703 - 4066 * t - 242 * wA) / 9204)
    - 767 / 1156 * (w - (3703 - 4066 * t - 242 * wA) / 9204) ^ 2 := by
  simp only [profitPool, stateProfitVI, poolQO1, poolQO2H, poolQI]; ring

/-- If `φ ≥ 0` (separating at least as good as the pooling cap) then `w̄sep/pool ≥ 0`. -/
lemma sepPool_nonneg_of (t wA : ℝ) (h : Standing t wA) (ht : t ≤ 0.401) (hp : 0 ≤ phif t wA) :
    0 ≤ wSepPool t wA := by
  obtain ⟨ht0, hw1, hw2⟩ := std_facts t wA h
  by_contra hneg; rw [not_le] at hneg
  have := sep4_lt t wA 0 (wSepPool t wA) hneg (by linarith)
  have := f10 t wA ht0.le ht hw1.le hw2.le
  rw [phif_eq] at hp; linarith

lemma pool_regime (t wA : ℝ) (h : Standing t wA) (hp : phif t wA ≤ 0) : SupAtPoolCap t wA := by
  obtain ⟨ht0, hw1, hw2⟩ := std_facts t wA h
  have hab := sepPool_lt_IBar t wA h
  have hbd := sepPool_lt_bound t wA h
  have hno := noProfit_lt_poolcap t wA h
  have hpe := phif_eq t wA
  set w0 := (3703 - 4066 * t - 242 * wA) / 9204 with hw0
  -- the pooling optimum lies above the cap
  have hw0b : wIBar t wA ≤ w0 := by
    by_contra hc; rw [not_le] at hc
    have h6 := f6 t wA h hc.le
    have hv := pool_vertex t wA (wIBar t wA)
    rw [← hw0] at hv h6
    have : 0 < (wIBar t wA - w0) ^ 2 := pow_pos (by linarith) 2
    linarith
  refine ⟨?_, limit_poolcap t wA h⟩
  intro wI hwI
  unfold profitVI
  split_ifs with h1 h2
  · -- separating piece
    have ha0 : 0 ≤ wSepPool t wA := le_trans hwI h1
    rw [← sep_at_pool t wA h ha0] at hpe
    have hmono := (lemma_4 t wA h).monotoneOn
    have : profitSep t wA wI ≤ profitSep t wA (wSepPool t wA) :=
      hmono ⟨hwI, by linarith⟩ ⟨ha0, hbd⟩ h1
    linarith
  · -- pooling piece
    have hv1 := pool_vertex t wA wI
    have hv2 := pool_vertex t wA (wIBar t wA)
    rw [← hw0] at hv1 hv2
    nlinarith [mul_nonneg (show (0:ℝ) ≤ wIBar t wA - wI by linarith) (show (0:ℝ) ≤ 2 * w0 - wI - wIBar t wA by linarith)]
  · linarith

lemma sep_regime (t wA : ℝ) (h : Standing t wA) (ht : t ≤ 0.401) (hp : 0 < phif t wA) :
    MaxAtSepPool t wA := by
  obtain ⟨ht0, hw1, hw2⟩ := std_facts t wA h
  have hab := sepPool_lt_IBar t wA h
  have hbd := sepPool_lt_bound t wA h
  have hno := noProfit_lt_poolcap t wA h
  have ha0 := sepPool_nonneg_of t wA h ht hp.le
  have hpe := phif_eq t wA
  rw [← sep_at_pool t wA h ha0] at hpe
  have hVa : profitVI t wA (wSepPool t wA) = profitSep t wA (wSepPool t wA) := by
    unfold profitVI; rw [if_pos le_rfl]
  refine ⟨ha0, ?_⟩
  intro wI hwI hne
  rw [hVa]
  unfold profitVI
  split_ifs with h1 h2
  · have hlt : wI < wSepPool t wA := lt_of_le_of_ne h1 hne
    exact (lemma_4 t wA h) ⟨hwI, by linarith⟩ ⟨ha0, hbd⟩ hlt
  · set w0 := (3703 - 4066 * t - 242 * wA) / 9204 with hw0
    have hv1 := pool_vertex t wA wI
    rw [← hw0] at hv1
    rcases le_or_gt (wIBar t wA) w0 with hc | hc
    · have hv2 := pool_vertex t wA (wIBar t wA)
      rw [← hw0] at hv2
      nlinarith [mul_nonneg (show (0:ℝ) ≤ wIBar t wA - wI by linarith) (show (0:ℝ) ≤ 2 * w0 - wI - wIBar t wA by linarith)]
    · have h6 := f6 t wA h hc.le
      rw [← hw0, ← sep_at_pool t wA h ha0] at h6
      nlinarith [sq_nonneg (wI - w0)]
  · linarith

end CSAux

theorem solution (tbar : ℝ) (htbar : tbar ≠ 0) (h7 : CoopetSourcing.WholesalePrice.Eq7 tbar) :
    (∀ t : ℝ, CoopetSourcing.WholesalePrice.tLow ≤ t → t < tbar →
      ∃ wAbar : ℝ, 0 < wAbar ∧
        CoopetSourcing.WholesalePrice.profitSep t wAbar (CoopetSourcing.WholesalePrice.wSepPool t wAbar) =
          CoopetSourcing.WholesalePrice.profitPool t wAbar (CoopetSourcing.WholesalePrice.wIBar t wAbar) ∧
        ∀ wA : ℝ, CoopetSourcing.WholesalePrice.Standing t wA →
          (wAbar < wA → CoopetSourcing.WholesalePrice.MaxAtSepPool t wA) ∧
          (wA ≤ wAbar → CoopetSourcing.WholesalePrice.SupAtPoolCap t wA)) ∧
    (∀ t wA : ℝ, tbar ≤ t → CoopetSourcing.WholesalePrice.Standing t wA →
      CoopetSourcing.WholesalePrice.SupAtPoolCap t wA) := by
  have htb := CSAux.tbar_lt tbar htbar h7
  have hlow := CSAux.wALow_lt
  have hw5 := CSAux.wALow_gt
  constructor
  · intro t ht htt
    have ht0 : (0.28:ℝ) ≤ t := le_trans CSAux.tLow_gt.le ht
    have ht1 : t ≤ 0.401 := by linarith
    set top := 1 / 2 - 5 * t / 7 with htop
    have hptop : 0 < CSAux.phif t top := (CSAux.phif_top_pos_iff tbar htbar h7 t ht0).mpr htt
    have hp01 : CSAux.phif t 0.01 < 0 := by
      rw [CSAux.phif_eq]
      have h8 := CSAux.f8 t ht0
      have := CSAux.sep4_lt t 0.01 0 (wSepPool t 0.01) h8 (by linarith)
      have := CSAux.f10 t 0.01 ht0 ht1 (by norm_num) (by linarith)
      linarith
    have hle : (0.01:ℝ) ≤ top := by linarith
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hle (CSAux.phif_cont t).continuousOn
      (show (0:ℝ) ∈ Set.Icc (CSAux.phif t 0.01) (CSAux.phif t top) from ⟨hp01.le, hptop.le⟩)
    have hc1 : (0.01:ℝ) < c := by
      rcases eq_or_lt_of_le hc.1 with h | h
      · rw [← h] at hc0; linarith
      · exact h
    have hc2 : c < top := by
      rcases eq_or_lt_of_le hc.2 with h | h
      · rw [h] at hc0; linarith
      · exact h
    have hstd : Standing t c := ⟨ht, by linarith, hc2⟩
    refine ⟨c, by linarith, ?_, ?_⟩
    · have ha0 := CSAux.sepPool_nonneg_of t c hstd ht1 hc0.ge
      rw [CSAux.sep_at_pool t c hstd ha0]
      have := CSAux.phif_eq t c; linarith
    · intro wA hwA
      have hwA' := CSAux.std_facts t wA hwA
      constructor
      · intro hlt
        apply CSAux.sep_regime t wA hwA ht1
        exact CSAux.phif_thresh t c wA ht0 (by linarith) (by linarith) hlt hwA.2.2.le hc0.ge
      · intro hle'
        apply CSAux.pool_regime t wA hwA
        rcases eq_or_lt_of_le hle' with h | h
        · rw [h, hc0]
        · by_contra hpos; rw [not_le] at hpos
          have := CSAux.phif_thresh t wA c ht0 (by linarith) (by linarith) h hc2.le hpos.le
          linarith
  · intro t wA ht hwA
    have hwA' := CSAux.std_facts t wA hwA
    apply CSAux.pool_regime t wA hwA
    by_contra hpos; rw [not_le] at hpos
    have ht0 : (0.28:ℝ) ≤ t := hwA'.1.le
    have := CSAux.phif_thresh t wA (1 / 2 - 5 * t / 7) ht0 (CSAux.t_lt_of_std t wA hwA) hwA'.2.1.le hwA'.2.2
      le_rfl hpos.le
    have := (CSAux.phif_top_pos_iff tbar htbar h7 t ht0).mp this
    linarith


