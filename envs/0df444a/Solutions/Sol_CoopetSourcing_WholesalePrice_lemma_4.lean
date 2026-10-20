-- Prove2me | solution 1 for CoopetSourcing.WholesalePrice.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:43:02.667547+00:00
-- url     : https://prove2.me/submissions/6a1f0e89-15f5-46f1-a787-496e415ec20a

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

def Nf (t wA w : ℝ) : ℝ := 36 * wA * (1 - wA) - 32 * w * (1 - w) - t * (14 + 32 * w - 60 * wA) - 17 * t ^ 2 - 1

lemma Nf_anti (t wA v w : ℝ) (h : v < w) (hw : w ≤ (1 + t) / 2) : Nf t wA w < Nf t wA v := by
  have : Nf t wA v - Nf t wA w = 32 * (w - v) * (1 + t - v - w) := by unfold Nf; ring
  nlinarith [mul_pos (sub_pos.mpr h) (show (0:ℝ) < 1 + t - v - w by linarith)]

lemma tLow_eq : tLow = 112 / 1105 + 28 * Real.sqrt 2 / 221 := by unfold tLow; ring

lemma Nf_06_neg (t wA : ℝ) (h : Standing t wA) : Nf t wA (3 / 5 * wA) < 0 := by
  obtain ⟨ht, hw1, hw2⟩ := h
  have hw0 := wALow_pos
  have hr : 0 ≤ t - tLow := by linarith
  rw [tLow_eq] at hr
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hq : 0 ≤ 71825 * t ^ 2 - 14560 * t - 1568 := by
    have : 71825 * t ^ 2 - 14560 * t - 1568 = 71825 * (t - (112 / 1105 + 28 * Real.sqrt 2 / 221))
        * (t - (112 / 1105 - 28 * Real.sqrt 2 / 221)) := by
      linear_combination ((71825:ℝ) * 784 / 48841) * hs2
    rw [this]
    apply mul_nonneg (mul_nonneg (by norm_num) hr); nlinarith
  have htop : Nf t wA (3 / 5 * wA) - Nf t (1 / 2 - 5 * t / 7) (3 / 5 * (1 / 2 - 5 * t / 7)) =
      -((1 / 2 - 5 * t / 7) - wA) * (84 / 5 + 204 / 5 * t - 612 / 25 * ((1 / 2 - 5 * t / 7) + wA)) := by
    unfold Nf; ring
  have hval : Nf t (1 / 2 - 5 * t / 7) (3 / 5 * (1 / 2 - 5 * t / 7)) = -(71825 * t ^ 2 - 14560 * t - 1568) / 1225 := by
    unfold Nf; ring
  have ht0 := tLow_gt
  nlinarith [mul_pos (show (0:ℝ) < (1 / 2 - 5 * t / 7) - wA by linarith)
    (show (0:ℝ) < 84 / 5 + 204 / 5 * t - 612 / 25 * ((1 / 2 - 5 * t / 7) + wA) by nlinarith)]

lemma Nf_nonneg_lt (t wA w : ℝ) (h : Standing t wA) (hw : w ≤ (1 + t) / 2) (hN : 0 ≤ Nf t wA w) :
    w < 3 / 5 * wA := by
  by_contra hc; rw [not_lt] at hc
  have h06 := Nf_06_neg t wA h
  rcases eq_or_lt_of_le hc with he | hlt
  · rw [← he] at hN; linarith
  · have := Nf_anti t wA (3 / 5 * wA) w hlt hw; linarith

noncomputable def h3f (t wA w : ℝ) : ℝ := profitSep4 t wA w + w * (Nf t wA w / (64 * (wA - w))) / 2

lemma quad_hasDeriv (a b c x : ℝ) : HasDerivAt (fun w => a + b * w + c * w ^ 2) (b + 2 * c * x) x := by
  have := ((hasDerivAt_id x).const_mul b).add ((hasDerivAt_pow 2 x).const_mul c)
  have h2 := this.const_add a
  refine (h2.congr_deriv (by simp; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [id, Pi.add_apply]; ring

lemma h3f_hasDeriv (t wA w : ℝ) (hw : w ≠ wA) :
    HasDerivAt (h3f t wA) (3 / 8 * (1 + t - 2 * w) +
      (wA * Nf t wA w + 16 * (wA - w) * (1 + t - 2 * w) * (3 * wA - 5 * w) - 48 * (1 + t - 2 * w) * (wA - w) ^ 2)
        / (128 * (wA - w) ^ 2)) w := by
  have hne : wA - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have h1 : HasDerivAt (fun w => profitSep4 t wA w) (3 / 8 * (1 + t - 2 * w)) w := by
    have := quad_hasDeriv (t^2/16 - t*wA/8 + wA^2/8 + wA/8 + 1/16) (3*t/8 + 3/8) (-3/8) w
    refine (this.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    simp only [profitSep4, stateProfitVI, sepQO1H, sepQIH]; ring
  have hN : HasDerivAt (fun w => Nf t wA w) (-32 * (1 + t - 2 * w)) w := by
    have := quad_hasDeriv (36 * wA * (1 - wA) - 14 * t + 60 * t * wA - 17 * t ^ 2 - 1) (-32 - 32 * t) 32 w
    refine (this.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    simp only [Nf]; ring
  have hD : HasDerivAt (fun w => 64 * (wA - w)) (-64) w := by
    have := ((hasDerivAt_id w).const_sub wA).const_mul 64
    refine (this.congr_deriv (by simp)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp
  have hq := hN.div hD (by intro h; apply hne; linarith)
  have hm := (hasDerivAt_id w).mul hq
  have htot := h1.add (hm.div_const 2)
  refine (htot.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · have h64 : (64 * (wA - w)) ≠ 0 := by intro h; apply hne; linarith
    simp only [id, Pi.div_apply]
    field_simp
    unfold Nf
    ring
  · simp only [h3f, id, Pi.add_apply, Pi.mul_apply, Pi.div_apply]

end CSAux



namespace CSAux

set_option maxHeartbeats 4000000

lemma bd_lt_wA (t wA : ℝ) (h : Standing t wA) : sepBound t wA < wA := by
  obtain ⟨ht, hw1, hw2⟩ := h
  have := tLow_gt
  have h6 : (2.449 : ℝ) < Real.sqrt 6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have := wALow_pos
  unfold sepBound
  have hm := mul_lt_mul_of_pos_right h6 (show (0:ℝ) < 7 + 10 * t - 14 * wA by linarith)
  have : Real.sqrt 6 * (7 + 10 * t - 14 * wA) / 35 = (Real.sqrt 6 * (7 + 10 * t - 14 * wA)) * (1 / 35) := by ring
  rw [this]
  linarith

lemma wA_pos (t wA : ℝ) (h : Standing t wA) : 0 < wA := lt_trans wALow_pos h.2.1

lemma wA_lt_half (t wA : ℝ) (h : Standing t wA) : wA < (1 + t) / 2 := by
  obtain ⟨ht, hw1, hw2⟩ := h; have := tLow_gt; linarith

lemma h3f_deriv_pos (t wA x : ℝ) (h : Standing t wA) (hx : x < wA) (hN : 0 ≤ Nf t wA x) :
    0 < 3 / 8 * (1 + t - 2 * x) +
      (wA * Nf t wA x + 16 * (wA - x) * (1 + t - 2 * x) * (3 * wA - 5 * x) - 48 * (1 + t - 2 * x) * (wA - x) ^ 2)
        / (128 * (wA - x) ^ 2) := by
  have hwA := wA_pos t wA h
  have hhalf := wA_lt_half t wA h
  have h06 := Nf_nonneg_lt t wA x h (by linarith) hN
  have hc : 0 < wA - x := by linarith
  have e : 3 / 8 * (1 + t - 2 * x) +
      (wA * Nf t wA x + 16 * (wA - x) * (1 + t - 2 * x) * (3 * wA - 5 * x) - 48 * (1 + t - 2 * x) * (wA - x) ^ 2)
        / (128 * (wA - x) ^ 2) =
      (wA * Nf t wA x + 16 * (wA - x) * (1 + t - 2 * x) * (3 * wA - 5 * x)) / (128 * (wA - x) ^ 2) := by
    field_simp; ring
  rw [e]
  apply div_pos _ (by positivity)
  have : 0 < 16 * (wA - x) * (1 + t - 2 * x) * (3 * wA - 5 * x) := by
    apply mul_pos (mul_pos (by linarith) (by linarith)); linarith
  nlinarith [mul_nonneg hwA.le hN]

lemma h3f_strictMono (t wA v u : ℝ) (h : Standing t wA) (hu : u < wA) (hNu : 0 ≤ Nf t wA u) :
    StrictMonoOn (h3f t wA) (Set.Icc v u) := by
  have hhalf := wA_lt_half t wA h
  apply strictMonoOn_of_deriv_pos (convex_Icc v u)
  · intro x hx
    exact (h3f_hasDeriv t wA x (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(h3f_hasDeriv t wA x (by linarith [hx.2])).deriv]
    have hN : 0 ≤ Nf t wA x := by
      have := Nf_anti t wA x u hx.2 (by linarith); linarith
    exact h3f_deriv_pos t wA x h (by linarith [hx.2]) hN

noncomputable def F3f (t wA w : ℝ) : ℝ := profitSep4 t wA w + w * max 0 (Nf t wA w / (64 * (wA - w))) / 2

lemma F3f_eq_h3 (t wA w : ℝ) (hw : w < wA) (hN : 0 ≤ Nf t wA w) : F3f t wA w = h3f t wA w := by
  unfold F3f h3f
  rw [max_eq_right (div_nonneg hN (by linarith))]

lemma F3f_eq_s4 (t wA w : ℝ) (hw : w < wA) (hN : Nf t wA w ≤ 0) : F3f t wA w = profitSep4 t wA w := by
  unfold F3f
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hN (by linarith))]; ring

lemma h3f_eq_s4 (t wA w : ℝ) (hN : Nf t wA w = 0) : h3f t wA w = profitSep4 t wA w := by
  unfold h3f; rw [hN]; ring

lemma sep4_lt' (t wA w v : ℝ) (h : v < w) (hw : w ≤ (1 + t) / 2) : profitSep4 t wA v < profitSep4 t wA w := by
  have : profitSep4 t wA w - profitSep4 t wA v = 3 / 8 * (w - v) * ((1 + t) - w - v) := by
    simp only [profitSep4, stateProfitVI, sepQO1H, sepQIH]; ring
  nlinarith [mul_pos (sub_pos.mpr h) (show (0:ℝ) < (1 + t) - w - v by linarith)]

lemma Nf_cont (t wA : ℝ) : Continuous (Nf t wA) := by unfold Nf; fun_prop

lemma F3f_strictMono (t wA : ℝ) (h : Standing t wA) (c : ℝ) (hc : c < wA) :
    StrictMonoOn (F3f t wA) (Set.Iio c) := by
  have hhalf := wA_lt_half t wA h
  intro v hv w hw hvw
  simp only [Set.mem_Iio] at hv hw
  rcases le_or_gt 0 (Nf t wA w) with hNw | hNw
  · have hNv : 0 ≤ Nf t wA v := by have := Nf_anti t wA v w hvw (by linarith); linarith
    rw [F3f_eq_h3 t wA v (by linarith) hNv, F3f_eq_h3 t wA w (by linarith) hNw]
    exact h3f_strictMono t wA v w h (by linarith) hNw ⟨le_rfl, hvw.le⟩ ⟨hvw.le, le_rfl⟩ hvw
  · rw [F3f_eq_s4 t wA w (by linarith) hNw.le]
    rcases le_or_gt (Nf t wA v) 0 with hNv | hNv
    · rw [F3f_eq_s4 t wA v (by linarith) hNv]
      exact sep4_lt' t wA w v hvw (by linarith)
    · obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc' hvw.le (Nf_cont t wA).continuousOn
        (show (0:ℝ) ∈ Set.Icc (Nf t wA w) (Nf t wA v) from ⟨hNw.le, hNv.le⟩)
      have hvu : v < u := by
        rcases eq_or_lt_of_le hu.1 with e | e
        · rw [← e] at hu0; linarith
        · exact e
      have huw : u < w := by
        rcases eq_or_lt_of_le hu.2 with e | e
        · rw [e] at hu0; linarith
        · exact e
      rw [F3f_eq_h3 t wA v (by linarith) hNv.le]
      have h1 := h3f_strictMono t wA v u h (by linarith) hu0.ge ⟨le_rfl, hvu.le⟩ ⟨hvu.le, le_rfl⟩ hvu
      rw [h3f_eq_s4 t wA u hu0] at h1
      have h2 := sep4_lt' t wA w u huw (by linarith)
      linarith

end CSAux



namespace CSAux

set_option maxHeartbeats 4000000

noncomputable def Ef (t wA w : ℝ) : ℝ := t ^ 2 + t * (2 + 24 * wA - 28 * w) + (1 + 4 * wA - 6 * w) ^ 2
noncomputable def q2f (t wA w : ℝ) : ℝ := Real.sqrt (2 * Ef t wA w) + 8 * w - 3 * t - 6 * wA - 1
noncomputable def f2f (t wA w : ℝ) : ℝ :=
  (stateProfitVI t w (sepQO1H t w) 0 (sepQIH t w) +
    stateProfitVI (-t) w (q2f t wA w) 0 ((1 - t - q2f t wA w) / 2)) / 2

noncomputable def alphaf (t wA w : ℝ) : ℝ := (19*t^2 - 246*t*w + 186*t*wA + 30*t + 360*w^2 - 468*w*wA - 126*w + 152*wA^2 + 82*wA + 11)
noncomputable def betaf (t wA w : ℝ) : ℝ := (-97*t/8 + 165*w/4 - 27*wA - 57/8)

lemma alpha_pos (t wA w : ℝ) (g1 : 0 ≤ t - 7/25) (g2 : 0 ≤ w) (g3 : 0 ≤ wA - w) (g4 : 0 ≤ 1/2 - 5*t/7 - wA) :
    0 < alphaf t wA w := by
  unfold alphaf
  linarith [g1, g2, g3, g4, (mul_nonneg g1 g1), (mul_nonneg g1 g2), (mul_nonneg g1 g3), (mul_nonneg g1 g4), (mul_nonneg g2 g2), (mul_nonneg g2 g3), (mul_nonneg g2 g4), (mul_nonneg g3 g3), (mul_nonneg g3 g4), (mul_nonneg g4 g4)]

lemma disc_pos (t wA w : ℝ) (g1 : 0 ≤ t - 7/25) (g2 : 0 ≤ w) (g3 : 0 ≤ wA - w) (g4 : 0 ≤ 1/2 - 5*t/7 - wA) :
    0 < (2143*t^4/32 + 1771*t^3*w/2 - 5193*t^3*wA/4 + 1651*t^3/8 + 16761*t^2*w^2/4 - 12093*t^2*w*wA/2 - 1167*t^2*w + 5563*t^2*wA^2/2 + 967*t^2*wA/4 + 3701*t^2/16 - 9810*t*w^3 + 14589*t*w^2*wA + 14841*t*w^2/2 - 6270*t*w*wA^2 - 8319*t*w*wA - 3261*t*w/2 + 600*t*wA^3 + 2235*t*wA^2 + 3849*t*wA/4 + 891*t/8 + 14175*w^4/2 - 13230*w^3*wA - 7560*w^3 + 7686*w^2*wA^2 + 12159*w^2*wA + 10521*w^2/4 - 1008*w*wA^3 - 6174*w*wA^2 - 5985*w*wA/2 - 378*w - 224*wA^4 + 952*wA^3 + 1659*wA^2/2 + 889*wA/4 + 623/32) := by
  linarith [g1, g2, g3, g4, (mul_nonneg g1 g1), (mul_nonneg g1 g2), (mul_nonneg g1 g3), (mul_nonneg g1 g4), (mul_nonneg g2 g2), (mul_nonneg g2 g3), (mul_nonneg g2 g4), (mul_nonneg g3 g3), (mul_nonneg g3 g4), (mul_nonneg g4 g4), (mul_nonneg (mul_nonneg g1 g1) g1), (mul_nonneg (mul_nonneg g1 g1) g2), (mul_nonneg (mul_nonneg g1 g1) g3), (mul_nonneg (mul_nonneg g1 g1) g4), (mul_nonneg (mul_nonneg g1 g2) g2), (mul_nonneg (mul_nonneg g1 g2) g3), (mul_nonneg (mul_nonneg g1 g2) g4), (mul_nonneg (mul_nonneg g1 g3) g3), (mul_nonneg (mul_nonneg g1 g3) g4), (mul_nonneg (mul_nonneg g1 g4) g4), (mul_nonneg (mul_nonneg g2 g2) g2), (mul_nonneg (mul_nonneg g2 g2) g3), (mul_nonneg (mul_nonneg g2 g2) g4), (mul_nonneg (mul_nonneg g2 g3) g3), (mul_nonneg (mul_nonneg g2 g3) g4), (mul_nonneg (mul_nonneg g2 g4) g4), (mul_nonneg (mul_nonneg g3 g3) g3), (mul_nonneg (mul_nonneg g3 g3) g4), (mul_nonneg (mul_nonneg g3 g4) g4), (mul_nonneg (mul_nonneg g4 g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g1), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g2), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g1) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g2) g2), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g2) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g3) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g1) g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g2) g2), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g2) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g3) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g3) g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g1 g3) g3) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g3) g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g1 g4) g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g2) g2), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g2) g3), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g2) g4), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g3) g4), (mul_nonneg (mul_nonneg (mul_nonneg g2 g2) g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g2 g3) g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g2 g3) g3) g4), (mul_nonneg (mul_nonneg (mul_nonneg g2 g3) g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g2 g4) g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g3 g3) g3) g3), (mul_nonneg (mul_nonneg (mul_nonneg g3 g3) g3) g4), (mul_nonneg (mul_nonneg (mul_nonneg g3 g3) g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g3 g4) g4) g4), (mul_nonneg (mul_nonneg (mul_nonneg g4 g4) g4) g4)]

lemma Ef_pos (t wA w : ℝ) (g1 : 0 ≤ t - 7/25) (g2 : 0 ≤ w) (g3 : 0 ≤ wA - w) (g4 : 0 ≤ 1/2 - 5*t/7 - wA) :
    0 < Ef t wA w := by
  unfold Ef
  linarith [g1, g2, g3, g4, (mul_nonneg g1 g1), (mul_nonneg g1 g2), (mul_nonneg g1 g3), (mul_nonneg g1 g4), (mul_nonneg g2 g2), (mul_nonneg g2 g3), (mul_nonneg g2 g4), (mul_nonneg g3 g3), (mul_nonneg g3 g4), (mul_nonneg g4 g4)]

lemma num_pos (t wA w : ℝ) (g1 : 0 ≤ t - 7/25) (g2 : 0 ≤ w) (g3 : 0 ≤ wA - w) (g4 : 0 ≤ 1/2 - 5*t/7 - wA) :
    0 < alphaf t wA w + betaf t wA w * Real.sqrt (2 * Ef t wA w) := by
  have ha := alpha_pos t wA w g1 g2 g3 g4
  have hd := disc_pos t wA w g1 g2 g3 g4
  have hE := Ef_pos t wA w g1 g2 g3 g4
  have hr := Real.sqrt_nonneg (2 * Ef t wA w)
  have hrs : Real.sqrt (2 * Ef t wA w) ^ 2 = 2 * Ef t wA w := Real.sq_sqrt (by linarith)
  have key : (betaf t wA w * Real.sqrt (2 * Ef t wA w)) ^ 2 < alphaf t wA w ^ 2 := by
    rw [mul_pow, hrs]; unfold alphaf betaf Ef; unfold Ef at hrs; nlinarith
  have h1 := abs_lt_of_sq_lt_sq key ha.le
  have h2 := neg_abs_le (betaf t wA w * Real.sqrt (2 * Ef t wA w))
  linarith

lemma f2f_eq (t wA : ℝ) : f2f t wA = fun w => ((t^2/32 + t/16 + 1/32) + (3*t/8 + 3/8) * w + (-3/8) * w ^ 2)
    + ((1 - t - q2f t wA w) / 2) ^ 2 / 2 + w * q2f t wA w / 2 := by
  funext w; unfold f2f; simp only [stateProfitVI, sepQO1H, sepQIH]; ring

lemma Ef_hasDeriv (t wA w : ℝ) : HasDerivAt (fun w => 2 * Ef t wA w) (2 * (-28 * t + 72 * w - 48 * wA - 12)) w := by
  have := quad_hasDeriv (2 * (t ^ 2 + 2 * t + 24 * t * wA + (1 + 4 * wA) ^ 2)) (2 * (-28 * t - 12 * (1 + 4 * wA))) 72 w
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  simp only [Ef]; ring

lemma f2f_hasDeriv (t wA w : ℝ) (hE : 0 < Ef t wA w) :
    HasDerivAt (f2f t wA) ((alphaf t wA w + betaf t wA w * Real.sqrt (2 * Ef t wA w)) / Real.sqrt (2 * Ef t wA w)) w := by
  have hrpos : 0 < Real.sqrt (2 * Ef t wA w) := Real.sqrt_pos.mpr (by linarith)
  have hrs : Real.sqrt (2 * Ef t wA w) ^ 2 = 2 * Ef t wA w := Real.sq_sqrt (by linarith)
  have hr := (Ef_hasDeriv t wA w).sqrt (by linarith)
  have hl := quad_hasDeriv (-3 * t - 6 * wA - 1) 8 0 w
  have hq : HasDerivAt (q2f t wA) (2 * (-28 * t + 72 * w - 48 * wA - 12) / (2 * Real.sqrt (2 * Ef t wA w)) + (8 + 2 * 0 * w)) w := by
    refine (hr.add hl).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    simp only [q2f, Pi.add_apply]; ring
  have h1 := quad_hasDeriv (t^2/32 + t/16 + 1/32) (3*t/8 + 3/8) (-3/8) w
  have h2 := (((hq.const_sub (1 - t)).div_const 2).pow 2).div_const 2
  have h3 := ((hasDerivAt_id w).mul hq).div_const 2
  have htot := (h1.add h2).add h3
  rw [f2f_eq]
  refine (htot.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · set r := Real.sqrt (2 * Ef t wA w) with hrdef
    have hr0 : r ≠ 0 := hrpos.ne'
    simp only [id, q2f]
    rw [← hrdef]
    field_simp
    unfold alphaf betaf
    unfold Ef at hrs
    linear_combination (80 : ℝ) * hrs
  · simp only [id, Pi.add_apply, Pi.pow_apply, Pi.mul_apply]

end CSAux



namespace CSAux

set_option maxHeartbeats 4000000

lemma f2f_strictMono (t wA c : ℝ) (h : Standing t wA) (hc : c < wA) :
    StrictMonoOn (f2f t wA) (Set.Icc 0 c) := by
  obtain ⟨ht0, hw1, hw2⟩ := std_facts t wA h
  have hEpos : ∀ x ∈ Set.Icc 0 c, 0 < Ef t wA x := fun x hx =>
    Ef_pos t wA x (by linarith) hx.1 (by linarith [hx.2]) (by linarith)
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 c)
  · intro x hx
    exact (f2f_hasDeriv t wA x (hEpos x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hE := hEpos x ⟨hx.1.le, hx.2.le⟩
    rw [(f2f_hasDeriv t wA x hE).deriv]
    apply div_pos (num_pos t wA x (by linarith) hx.1.le (by linarith [hx.2]) (by linarith))
    exact Real.sqrt_pos.mpr (by linarith)

lemma sep_branch2 (t wA w : ℝ) (h : Standing t wA) (hw0 : 0 ≤ w) (hw : w ≤ wSep2 t wA) :
    profitSep t wA w = f2f t wA w := by
  have h1 := sep1_neg t wA h
  have hQ1 : sepQO1L t wA w = q2f t wA w := by
    unfold sepQO1L; rw [if_neg (by linarith), if_pos hw]; rfl
  have hQ2 : sepQO2L t wA w = 0 := by unfold sepQO2L; rw [if_pos hw]
  have hQI : sepQIL t wA w = (1 - t - q2f t wA w) / 2 := by unfold sepQIL; rw [if_pos hw, hQ1]
  unfold profitSep f2f; rw [hQ1, hQ2, hQI]

lemma sep_branch3 (t wA w : ℝ) (h : Standing t wA) (hw0 : 0 ≤ w) (hw : wSep2 t wA < w) :
    profitSep t wA w = F3f t wA w := by
  have h1 := sep1_neg t wA h
  have hQ1 : sepQO1L t wA w = max 0 (Nf t wA w / (64 * (wA - w))) := by
    unfold sepQO1L; rw [if_neg (by linarith), if_neg (by linarith)]; rfl
  have hQ2 : sepQO2L t wA w = (1 - t - 2 * wA) / 2 - max 0 (Nf t wA w / (64 * (wA - w))) := by
    unfold sepQO2L; rw [if_neg (by linarith), hQ1]
  have hQI : sepQIL t wA w = (1 - t + 2 * wA) / 4 := by unfold sepQIL; rw [if_neg (by linarith)]
  unfold profitSep F3f; rw [hQ1, hQ2, hQI]
  simp only [profitSep4, stateProfitVI, sepQO1H, sepQIH]; ring

lemma wSep2_eq (t wA : ℝ) : wSep2 t wA = t + wA - (1 + 7 * t - 2 * wA) * Real.sqrt 2 / 8 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  unfold wSep2; field_simp; linear_combination ((1 + 7 * t - 2 * wA) * 4 : ℝ) * hs

lemma junction (t wA : ℝ) (h : Standing t wA) : f2f t wA (wSep2 t wA) = F3f t wA (wSep2 t wA) := by
  obtain ⟨ht0, hw1, hw2⟩ := std_facts t wA h
  obtain ⟨r1, r2⟩ := sqrt2_bounds
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlt : wSep2 t wA < wA := by rw [wSep2_eq]; nlinarith
  set u := Real.sqrt 2 with hu
  set m0 := (1 - t - 2 * wA) / 2 with hm0
  have hN : Nf t wA (wSep2 t wA) / (64 * (wA - wSep2 t wA)) = m0 := by
    rw [div_eq_iff (by linarith)]
    rw [wSep2_eq, ← hu, hm0]; unfold Nf
    linear_combination ((7 * t - 2 * wA + 1) ^ 2 / 2 : ℝ) * hs
  have htg : 0 ≤ (-11 * t + 14 * u * t - 6 * wA - 4 * u * wA + 2 * u + 3) / 2 := by nlinarith
  have hq : q2f t wA (wSep2 t wA) = m0 := by
    unfold q2f
    have : Real.sqrt (2 * Ef t wA (wSep2 t wA)) = (-11 * t + 14 * u * t - 6 * wA - 4 * u * wA + 2 * u + 3) / 2 := by
      rw [← Real.sqrt_sq htg]; congr 1
      rw [wSep2_eq, ← hu]; unfold Ef
      linear_combination ((7 * t - 2 * wA + 1) ^ 2 / 8 : ℝ) * hs
    rw [this, wSep2_eq, ← hu, hm0]; ring
  have hm0pos : 0 ≤ m0 := by rw [hm0]; linarith
  unfold f2f F3f
  rw [hq, hN, max_eq_right hm0pos, hm0]
  simp only [profitSep4, stateProfitVI, sepQO1H, sepQIH]; ring

end CSAux

open CSAux in
theorem lemma4_proof (t wA : ℝ) (h : CoopetSourcing.WholesalePrice.Standing t wA) :
    StrictMonoOn (CoopetSourcing.WholesalePrice.profitSep t wA)
      (Set.Ico 0 (CoopetSourcing.WholesalePrice.sepBound t wA)) := by
  have hbd := bd_lt_wA t wA h
  have hs2 : wSep2 t wA < sepBound t wA :=
    lt_trans (sep2_lt_sepPool t wA h) (sepPool_lt_bound t wA h)
  have hF3 := F3f_strictMono t wA h (sepBound t wA) hbd
  intro v hv w hw hvw
  rcases le_or_gt w (wSep2 t wA) with hw2 | hw2
  · rw [sep_branch2 t wA v h hv.1 (by linarith), sep_branch2 t wA w h hw.1 hw2]
    exact f2f_strictMono t wA (wSep2 t wA) h (by linarith) ⟨hv.1, by linarith⟩ ⟨hw.1, hw2⟩ hvw
  · rw [sep_branch3 t wA w h hw.1 hw2]
    rcases le_or_gt v (wSep2 t wA) with hv2 | hv2
    · rw [sep_branch2 t wA v h hv.1 hv2]
      have h1 : f2f t wA v ≤ f2f t wA (wSep2 t wA) :=
        (f2f_strictMono t wA (wSep2 t wA) h (by linarith)).monotoneOn ⟨hv.1, hv2⟩ ⟨le_trans hv.1 hv2, le_rfl⟩ hv2
      rw [junction t wA h] at h1
      have h2 : F3f t wA (wSep2 t wA) < F3f t wA w := hF3 (show wSep2 t wA < sepBound t wA from hs2) hw.2 hw2
      linarith
    · rw [sep_branch3 t wA v h hv.1 hv2]
      exact hF3 hv.2 hw.2 hvw


theorem solution (t wA : ℝ) (h : CoopetSourcing.WholesalePrice.Standing t wA) :
    StrictMonoOn (CoopetSourcing.WholesalePrice.profitSep t wA)
      (Set.Ico 0 (CoopetSourcing.WholesalePrice.sepBound t wA)) :=
  lemma4_proof t wA h

