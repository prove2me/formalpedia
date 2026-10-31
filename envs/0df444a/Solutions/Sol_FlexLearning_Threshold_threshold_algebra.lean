-- Prove2me | solution 1 for FlexLearning.Threshold.threshold_algebra
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:47:42.704423+00:00
-- url     : https://prove2.me/submissions/57efba12-65a2-4fe3-80ee-8828a48a40ce

import Mathlib
import Theorems.Thm_FlexLearning_Threshold_aux_poly_bounds

set_option maxHeartbeats 2000000

namespace FlexAnal

noncomputable def nfun (w : ℝ) : ℝ := 1 - w ^ 2 + w ^ 3 / 3
noncomputable def Tp (w : ℝ) : ℝ :=
  9 * w ^ 8 - 72 * w ^ 7 + 196 * w ^ 6 - 237 * w ^ 5 + 261 * w ^ 4 - 372 * w ^ 3 + 72 * w ^ 2 +
    432 * w - 288

lemma Tp_hasDeriv (w : ℝ) : HasDerivAt Tp (72 * w ^ 7 - 504 * w ^ 6 + 1176 * w ^ 5 - 1185 * w ^ 4
    + 1044 * w ^ 3 - 1116 * w ^ 2 + 144 * w + 432) w := by
  unfold Tp
  have h := fun (n : ℕ) => hasDerivAt_pow n w
  have := ((((((((((h 8).const_mul 9).sub ((h 7).const_mul 72)).add ((h 6).const_mul 196)).sub
    ((h 5).const_mul 237)).add ((h 4).const_mul 261)).sub ((h 3).const_mul 372)).add
    ((h 2).const_mul 72)).add ((hasDerivAt_id w).const_mul 432)).sub_const 288)
  refine (this.congr_deriv (by norm_num; ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun x => ?_))
  simp

lemma P12_pos (s : ℝ) (h0 : (0:ℝ) ≤ s) (h1 : s ≤ ((289:ℝ)/500)) :
    0 < (8:ℝ) + (36:ℝ) * s ^ 1 + (54:ℝ) * s ^ 2 + (-429:ℝ) * s ^ 3 + (162:ℝ) * s ^ 5 + (1314:ℝ) * s ^ 6 + (-648:ℝ) * s ^ 7 + (-486:ℝ) * s ^ 8 + (-1053:ℝ) * s ^ 9 + (972:ℝ) * s ^ 10 + (81:ℝ) * s ^ 12 :=
  FlexLearning.Threshold.aux_poly_bounds.1 _ h0 h1

lemma PH_pos (s : ℝ) (h0 : ((1:ℝ)/2) ≤ s) (h1 : s ≤ ((289:ℝ)/500)) :
    0 < (-1:ℝ) + (24:ℝ) * s ^ 3 + (54:ℝ) * s ^ 4 + (-558:ℝ) * s ^ 6 + (162:ℝ) * s ^ 7 + (-243:ℝ) * s ^ 8 + (972:ℝ) * s ^ 9 + (3888:ℝ) * s ^ 10 + (-2916:ℝ) * s ^ 11 + (-7290:ℝ) * s ^ 12 + (4374:ℝ) * s ^ 13 + (2187:ℝ) * s ^ 14 + (24057:ℝ) * s ^ 15 + (-65610:ℝ) * s ^ 16 + (39366:ℝ) * s ^ 17 + (-19683:ℝ) * s ^ 18 + (78732:ℝ) * s ^ 19 + (-59049:ℝ) * s ^ 20 :=
  FlexLearning.Threshold.aux_poly_bounds.2.1 _ h0 h1

lemma Td_pos (w : ℝ) (h0 : (0:ℝ) ≤ w) (h1 : w ≤ (1:ℝ)) :
    0 < (432:ℝ) + (144:ℝ) * w ^ 1 + (-1116:ℝ) * w ^ 2 + (1044:ℝ) * w ^ 3 + (-1185:ℝ) * w ^ 4 + (1176:ℝ) * w ^ 5 + (-504:ℝ) * w ^ 6 + (72:ℝ) * w ^ 7 :=
  FlexLearning.Threshold.aux_poly_bounds.2.2.1 _ h0 h1

lemma al9_pos (w : ℝ) (h0 : (0:ℝ) ≤ w) (h1 : w ≤ (1:ℝ)) :
    0 < (144:ℝ) + (-252:ℝ) * w ^ 2 + (72:ℝ) * w ^ 3 + (117:ℝ) * w ^ 4 + (-54:ℝ) * w ^ 5 + (-4:ℝ) * w ^ 6 + (3:ℝ) * w ^ 7 :=
  FlexLearning.Threshold.aux_poly_bounds.2.2.2.1 _ h0 h1

lemma be3n_pos (w : ℝ) (h0 : (0:ℝ) ≤ w) (h1 : w ≤ (1:ℝ)) :
    0 < (48:ℝ) + (-60:ℝ) * w ^ 2 + (16:ℝ) * w ^ 3 + (15:ℝ) * w ^ 4 + (-4:ℝ) * w ^ 5 :=
  FlexLearning.Threshold.aux_poly_bounds.2.2.2.2 _ h0 h1

lemma Tp_strictMono : StrictMonoOn Tp (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · exact (by unfold Tp; fun_prop : Continuous Tp).continuousOn
  · intro w hw
    rw [interior_Icc] at hw
    rw [(Tp_hasDeriv w).deriv]
    have := Td_pos w (by norm_num; linarith [hw.1]) (by norm_num; linarith [hw.2])
    simp only [pow_one] at this
    linarith

lemma Tp_root : ∃ w0 : ℝ, 49 / 50 ≤ w0 ∧ w0 ≤ 99 / 100 ∧ Tp w0 = 0 := by
  have hc : ContinuousOn Tp (Set.Icc (49 / 50) (99 / 100)) :=
    (by unfold Tp; fun_prop : Continuous Tp).continuousOn
  have h1 : Tp (49 / 50) < 0 := by unfold Tp; norm_num
  have h2 : 0 < Tp (99 / 100) := by unfold Tp; norm_num
  obtain ⟨w0, hw0, hv⟩ := intermediate_value_Icc (by norm_num) hc ⟨h1.le, h2.le⟩
  exact ⟨w0, hw0.1, hw0.2, hv⟩

lemma nfun_anti (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : nfun b < nfun a := by
  unfold nfun
  have h : nfun a - nfun b = (b - a) * ((a + b) - (a ^ 2 + a * b + b ^ 2) / 3) := by
    unfold nfun; ring
  have ha2 : a * a ≤ a * 1 := mul_le_mul_of_nonneg_left (by linarith) ha
  have hab2 : a * b ≤ 1 * b := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hb2 : b * b ≤ b * 1 := mul_le_mul_of_nonneg_left hb (by linarith)
  have h2 : (a ^ 2 + a * b + b ^ 2) / 3 < a + b := by
    have e : a ^ 2 + a * b + b ^ 2 = a * a + a * b + b * b := by ring
    rw [e]; linarith
  have : 0 < (b - a) * ((a + b) - (a ^ 2 + a * b + b ^ 2) / 3) :=
    mul_pos (by linarith) (by linarith)
  unfold nfun at h
  linarith

/-- Region II core: comparison of the optimal flexible value with `V_N`. -/
lemma regII_core (m w r : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 1) (hm0 : 0 < m) (hm1 : m ≤ 1)
    (hn : m ^ 2 = nfun w) (hr0 : 0 < r) (hr : r ^ 2 = 1 + m - m ^ 2) :
    (0 ≤ Tp w → m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2) ≤ 1 + m - w ^ 2 + w ^ 3 / (3 * r)) ∧
    (Tp w < 0 → 1 + m - w ^ 2 + w ^ 3 / (3 * r) ≤ m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2)) := by
  unfold nfun at hn
  -- the gap (w ^ 3 / 3) - ((1 - m) ^ 2) > 0
  have hgap : ((1 - m) ^ 2) < (w ^ 3 / 3) := by
    have hw21 : w ^ 2 ≤ 1 := pow_le_one₀ hw0.le hw1
    have h2w : 0 < 2 - w ^ 2 := by linarith
    have hsq : (2 - w ^ 2) ^ 2 < (2 * m) ^ 2 := by
      have : (2 * m) ^ 2 = 4 * (1 - w ^ 2 + w ^ 3 / 3) := by rw [mul_pow, hn]; ring
      rw [this]
      have e : 4 * (1 - w ^ 2 + w ^ 3 / 3) - (2 - w ^ 2) ^ 2 = w ^ 3 * (4 / 3 - w) := by ring
      have : 0 < w ^ 3 * (4 / 3 - w) := mul_pos (pow_pos hw0 3) (by linarith)
      linarith
    have : 2 - w ^ 2 < 2 * m := (pow_lt_pow_iff_left₀ h2w.le (by linarith) (by norm_num)).1 hsq
    have e : (1 - m) ^ 2 = 1 - 2 * m + m ^ 2 := by ring
    rw [e, hn]; linarith
  have hP0 : 0 ≤ ((1 - m) ^ 2) := sq_nonneg _
  have hA : 1 + m - m ^ 2 = r ^ 2 := hr.symm
  -- the numerator identity
  have hden : 0 < r ^ 2 * (r + 1) := by positivity
  have hdiff : 1 + m - w ^ 2 + w ^ 3 / (3 * r) - m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2) =
      m * (1 - m) * (((1 - m) ^ 2) * (r + 1) - (w ^ 3 / 3) * r) / (r ^ 2 * (r + 1)) := by
    rw [hA]
    have hnum : (1 + m - w ^ 2) * r ^ 2 * (r + 1) + w ^ 3 / 3 * r * (r + 1) -
        m ^ 2 * (5 - 3 * m) * (r + 1) = m * (1 - m) * (((1 - m) ^ 2) * (r + 1) - (w ^ 3 / 3) * r) := by
      linear_combination (m * r + m - r * w ^ 2 + r + w ^ 3 / 3 - w ^ 2 + 1) * hr +
        (m ^ 2 * r + m ^ 2 - m * r - m - r - 1) * hn
    rw [← hnum]
    field_simp
    try ring
  have hmm : 0 ≤ m * (1 - m) := mul_nonneg hm0.le (by linarith)
  -- algebraic reduction of the sign of E' = ((1 - m) ^ 2) (r+1) - (w ^ 3 / 3) r
  set α := (3 * w ^ 7 - 4 * w ^ 6 - 54 * w ^ 5 + 117 * w ^ 4 + 72 * w ^ 3 - 252 * w ^ 2 + 144) / 9
    with hα
  set β := (4 * w ^ 5 - 15 * w ^ 4 - 16 * w ^ 3 + 60 * w ^ 2 - 48) / 3 with hβ
  have hαpos : 0 < α := by
    have := al9_pos w hw0.le hw1; (try simp only [pow_one] at this); rw [hα]; linarith
  have hβneg : β < 0 := by
    have := be3n_pos w hw0.le hw1; (try simp only [pow_one] at this); rw [hβ]; linarith
  have hPw : β ^ 2 * (1 - w ^ 2 + w ^ 3 / 3) - α ^ 2 = -(w ^ 6 * Tp w) / 81 := by
    rw [hα, hβ]; unfold Tp; ring
  have hP1 : ((1 - m) ^ 2) ^ 2 - ((w ^ 3 / 3) - ((1 - m) ^ 2)) ^ 2 * (1 + m - m ^ 2) = α + β * m := by
    rw [hα, hβ]
    linear_combination (m ^ 4 - 5 * m ^ 3 + m ^ 2 * (-w ^ 3 / 3 - w ^ 2 + 11) +
      m * (w ^ 3 / 3 + 5 * w ^ 2 - 15) + w ^ 4 + 2 * w ^ 3 - 12 * w ^ 2 + 16) * hn
  have hKPr : 0 ≤ ((w ^ 3 / 3) - ((1 - m) ^ 2)) * r := mul_nonneg (by linarith) hr0.le
  have hw6 : 0 < w ^ 6 := by positivity
  have hbm : 0 ≤ -β * m := mul_nonneg (by linarith) hm0.le
  constructor
  · intro hT
    have h1 : (-β * m) ^ 2 ≤ α ^ 2 := by
      have : (-β * m) ^ 2 = β ^ 2 * (1 - w ^ 2 + w ^ 3 / 3) := by rw [mul_pow, hn]; ring
      rw [this]
      have : 0 ≤ w ^ 6 * Tp w := mul_nonneg hw6.le hT
      linarith
    have h2 : -β * m ≤ α := (pow_le_pow_iff_left₀ hbm hαpos.le (by norm_num)).1 h1
    have h3 : (((w ^ 3 / 3) - ((1 - m) ^ 2)) * r) ^ 2 ≤ ((1 - m) ^ 2) ^ 2 := by
      have : (((w ^ 3 / 3) - ((1 - m) ^ 2)) * r) ^ 2 = ((w ^ 3 / 3) - ((1 - m) ^ 2)) ^ 2 * (1 + m - m ^ 2) := by rw [mul_pow, hr]
      rw [this]; linarith
    have h4 : ((w ^ 3 / 3) - ((1 - m) ^ 2)) * r ≤ ((1 - m) ^ 2) := (pow_le_pow_iff_left₀ hKPr hP0 (by norm_num)).1 h3
    have hE : 0 ≤ ((1 - m) ^ 2) * (r + 1) - (w ^ 3 / 3) * r := by
      have e : ((1 - m) ^ 2) * (r + 1) - (w ^ 3 / 3) * r =
          ((1 - m) ^ 2) - ((w ^ 3 / 3) - ((1 - m) ^ 2)) * r := by ring
      rw [e]; linarith
    have : 0 ≤ m * (1 - m) * (((1 - m) ^ 2) * (r + 1) - (w ^ 3 / 3) * r) / (r ^ 2 * (r + 1)) :=
      div_nonneg (mul_nonneg hmm hE) hden.le
    linarith
  · intro hT
    have h1 : α ^ 2 < (-β * m) ^ 2 := by
      have : (-β * m) ^ 2 = β ^ 2 * (1 - w ^ 2 + w ^ 3 / 3) := by rw [mul_pow, hn]; ring
      rw [this]
      have : w ^ 6 * Tp w < 0 := mul_neg_of_pos_of_neg hw6 hT
      linarith
    have h2 : α < -β * m := (pow_lt_pow_iff_left₀ hαpos.le hbm (by norm_num)).1 h1
    have h3 : ((1 - m) ^ 2) ^ 2 < (((w ^ 3 / 3) - ((1 - m) ^ 2)) * r) ^ 2 := by
      have : (((w ^ 3 / 3) - ((1 - m) ^ 2)) * r) ^ 2 = ((w ^ 3 / 3) - ((1 - m) ^ 2)) ^ 2 * (1 + m - m ^ 2) := by rw [mul_pow, hr]
      rw [this]; linarith
    have h4 : ((1 - m) ^ 2) < ((w ^ 3 / 3) - ((1 - m) ^ 2)) * r := (pow_lt_pow_iff_left₀ hP0 hKPr (by norm_num)).1 h3
    have hE : ((1 - m) ^ 2) * (r + 1) - (w ^ 3 / 3) * r ≤ 0 := by
      have e : ((1 - m) ^ 2) * (r + 1) - (w ^ 3 / 3) * r =
          ((1 - m) ^ 2) - ((w ^ 3 / 3) - ((1 - m) ^ 2)) * r := by ring
      rw [e]; linarith
    have : m * (1 - m) * (((1 - m) ^ 2) * (r + 1) - (w ^ 3 / 3) * r) / (r ^ 2 * (r + 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hmm hE) hden.le
    linarith


noncomputable def Ln (m f q : ℝ) : ℝ := m ^ 2 + q * ((1 + m - m ^ 2) - f) - (1 + m - m ^ 2) * q ^ 3 / 6
noncomputable def Hn (m f u : ℝ) : ℝ := 1 + m - 2 * f + f * u - (1 + m - m ^ 2) * u ^ 3 / 6
noncomputable def phi (m f q : ℝ) : ℝ :=
  if q ≤ 1 then Ln m f q else if q ≤ 2 then Hn m f (2 - q) else Hn m f 0 - f * (q - 2)
noncomputable def VNn (m : ℝ) : ℝ := m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2)
noncomputable def gn (f : ℝ) : ℝ :=
  if 2 * f ≤ 1 then 2 / 3 * f * (Real.sqrt (2 * f) - 3) + 1
  else 2 / 3 * (1 - f) * Real.sqrt (2 - 2 * f)

lemma Ln_one (m f : ℝ) : Ln m f 1 = Hn m f 1 := by unfold Ln Hn; ring

lemma phi_H (m f u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : phi m f (2 - u) = Hn m f u := by
  unfold phi
  split_ifs with h1 h2
  · have : u = 1 := by linarith
    subst this; rw [show (2:ℝ) - 1 = 1 by norm_num, Ln_one]
  · congr 1; ring
  · exfalso; linarith

lemma Hn_le (m f y u : ℝ) (hy0 : 0 ≤ y) (hu : 0 ≤ u) (hf : f = (1 + m - m ^ 2) * y ^ 2 / 2)
    (hA : 0 ≤ 1 + m - m ^ 2) : Hn m f u ≤ Hn m f y := by
  unfold Hn
  have : 1 + m - 2 * f + f * y - (1 + m - m ^ 2) * y ^ 3 / 6 -
      (1 + m - 2 * f + f * u - (1 + m - m ^ 2) * u ^ 3 / 6) =
      (1 + m - m ^ 2) / 6 * ((u - y) ^ 2 * (u + 2 * y)) := by rw [hf]; ring
  have : 0 ≤ (1 + m - m ^ 2) / 6 * ((u - y) ^ 2 * (u + 2 * y)) := by
    apply mul_nonneg (by linarith); apply mul_nonneg (sq_nonneg _); linarith
  linarith

lemma regII_upper (m f y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hf : f = (1 + m - m ^ 2) * y ^ 2 / 2)
    (hA : 1 ≤ 1 + m - m ^ 2) : ∀ q, 0 ≤ q → phi m f q ≤ Hn m f y := by
  intro q hq
  have hf0 : 0 ≤ f := by rw [hf]; positivity
  have hfA : f ≤ (1 + m - m ^ 2) / 2 := by
    rw [hf]; have : y ^ 2 ≤ 1 := pow_le_one₀ hy0 hy1
    have := mul_le_mul_of_nonneg_left this (show (0:ℝ) ≤ 1 + m - m ^ 2 by linarith)
    linarith
  unfold phi
  split_ifs with h1 h2
  · have : Ln m f q ≤ Ln m f 1 := by
      unfold Ln
      have e : m ^ 2 + 1 * ((1 + m - m ^ 2) - f) - (1 + m - m ^ 2) * 1 ^ 3 / 6 -
          (m ^ 2 + q * ((1 + m - m ^ 2) - f) - (1 + m - m ^ 2) * q ^ 3 / 6) =
          (1 - q) * ((1 + m - m ^ 2) - f - (1 + m - m ^ 2) * (1 + q + q ^ 2) / 6) := by ring
      have : 0 ≤ (1 - q) * ((1 + m - m ^ 2) - f - (1 + m - m ^ 2) * (1 + q + q ^ 2) / 6) := by
        apply mul_nonneg (by linarith)
        have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ hq h1
        have : 1 + q + q ^ 2 ≤ 3 := by linarith
        have := mul_le_mul_of_nonneg_left this (show (0:ℝ) ≤ 1 + m - m ^ 2 by linarith)
        linarith
      linarith
    rw [Ln_one] at this
    linarith [Hn_le m f y 1 hy0 (by norm_num) hf (by linarith)]
  · exact Hn_le m f y (2 - q) hy0 (by linarith) hf (by linarith)
  · have := Hn_le m f y 0 hy0 le_rfl hf (by linarith)
    have : 0 ≤ f * (q - 2) := mul_nonneg hf0 (by linarith)
    linarith

lemma regI (m z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) (hm0 : 0 < m) (hmz : m ^ 2 = z ^ 3 / 3) :
    ∃ q, 0 ≤ q ∧ VNn m ≤ phi m (1 - z ^ 2 / 2) q := by
  set s := m / z with hs
  have hms : m = s * z := by rw [hs]; field_simp
  have hzs : z = 3 * s ^ 2 := by
    have h1 : z ^ 3 = 3 * (s * z) ^ 2 := by rw [← hms]; linarith
    have h2 : z ^ 2 * (z - 3 * s ^ 2) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · exfalso; have : 0 < z ^ 2 := by positivity
      linarith
    · linarith
  have hm3 : m = 3 * s ^ 3 := by rw [hms, hzs]; ring
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s ≤ 289 / 500 := by
    by_contra h; push Not at h
    have : (289 / 500 : ℝ) ^ 2 < s ^ 2 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    rw [hzs] at hz1; norm_num at this; linarith
  set f := 1 - z ^ 2 / 2 with hfdef
  have hf : f = 1 - 9 * s ^ 4 / 2 := by rw [hfdef, hzs]; ring
  set A := 1 + m - m ^ 2 with hAdef
  have hm1 : m ≤ 1 := by
    rw [hm3]; have : s ^ 3 ≤ (289 / 500) ^ 3 := pow_le_pow_left₀ hs0.le hs1 3
    norm_num at this; linarith
  have hA1 : 1 ≤ A := by
    rw [hAdef]; have : 0 ≤ m * (1 - m) := mul_nonneg hm0.le (by linarith)
    have e : 1 + m - m ^ 2 = 1 + m * (1 - m) := by ring
    rw [e]; linarith
  have hf1 : f < 1 := by rw [hf]; have : 0 < s ^ 4 := by positivity
                         linarith
  have hf0 : 0 < f := by
    rw [hf]; have : s ^ 4 ≤ (289 / 500) ^ 4 := pow_le_pow_left₀ hs0.le hs1 4
    norm_num at this; linarith
  have hA0 : A ≠ 0 := by linarith
  have hVN : VNn m = m ^ 2 + m ^ 2 * (2 - m) ^ 2 / A := by
    unfold VNn; rw [← hAdef]; field_simp; ring
  rcases le_total A (2 * f) with hc | hc
  · -- interior optimum of the low regime
    set q := Real.sqrt (2 * (A - f) / A) with hq
    have hAf : 0 < A - f := by linarith
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hq2 : q ^ 2 = 2 * (A - f) / A := Real.sq_sqrt (by positivity)
    have hq1 : q ≤ 1 := by
      rw [hq, Real.sqrt_le_one]
      rw [div_le_one (by linarith)]; linarith
    refine ⟨q, hq0, ?_⟩
    unfold phi; rw [if_pos hq1]
    have hL : Ln m f q = m ^ 2 + 2 / 3 * (A - f) * q := by
      unfold Ln; rw [← hAdef]
      have : q ^ 3 = q * (2 * (A - f) / A) := by rw [← hq2]; ring
      rw [this]; field_simp; try ring
    rw [hL, hVN]
    have hlhs : 0 ≤ 2 / 3 * (A - f) * q := by positivity
    have hrhs : 0 ≤ m ^ 2 * (2 - m) ^ 2 / A := by positivity
    have hsq : (m ^ 2 * (2 - m) ^ 2 / A) ^ 2 ≤ (2 / 3 * (A - f) * q) ^ 2 := by
      have e1 : (2 / 3 * (A - f) * q) ^ 2 = 8 * (A - f) ^ 3 * A / (9 * A ^ 2) := by
        rw [mul_pow, hq2]; field_simp; ring
      have e2 : (m ^ 2 * (2 - m) ^ 2 / A) ^ 2 = 9 * m ^ 4 * (2 - m) ^ 4 / (9 * A ^ 2) := by
        field_simp; try ring
      rw [e1, e2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hid : 8 * (A - f) ^ 3 * A - 9 * m ^ 4 * (2 - m) ^ 4 =
          27 * s ^ 9 * (1 - 3 * s ^ 3) * (8 + 36 * s ^ 1 + 54 * s ^ 2 + (-429) * s ^ 3 +
            162 * s ^ 5 + 1314 * s ^ 6 + (-648) * s ^ 7 + (-486) * s ^ 8 + (-1053) * s ^ 9 +
            972 * s ^ 10 + 81 * s ^ 12) := by
        rw [hAdef, hf, hm3]; ring
      have hP := P12_pos s hs0.le hs1
      have h3 : 0 < 1 - 3 * s ^ 3 := by
        have : s ^ 3 ≤ (289 / 500) ^ 3 := pow_le_pow_left₀ hs0.le hs1 3
        norm_num at this; linarith
      have : 0 ≤ 27 * s ^ 9 * (1 - 3 * s ^ 3) * (8 + 36 * s ^ 1 + 54 * s ^ 2 + (-429) * s ^ 3 +
            162 * s ^ 5 + 1314 * s ^ 6 + (-648) * s ^ 7 + (-486) * s ^ 8 + (-1053) * s ^ 9 +
            972 * s ^ 10 + 81 * s ^ 12) := by
        apply mul_nonneg (mul_nonneg (by positivity) h3.le)
        norm_num at hP ⊢; linarith
      linarith
    have := (pow_le_pow_iff_left₀ hrhs hlhs (by norm_num)).1 hsq
    linarith
  · -- interior optimum of the high regime
    have hshalf : 1 / 2 ≤ s := by
      by_contra h; push Not at h
      have h3 : s ^ 3 < (1 / 2) ^ 3 := pow_lt_pow_left₀ h hs0.le (by norm_num)
      have h4 : s ^ 4 < (1 / 2) ^ 4 := pow_lt_pow_left₀ h hs0.le (by norm_num)
      have : A - 2 * f < 0 := by
        rw [hAdef, hf, hm3]
        have e : 1 + 3 * s ^ 3 - (3 * s ^ 3) ^ 2 - 2 * (1 - 9 * s ^ 4 / 2) =
            9 * s ^ 4 + 3 * s ^ 3 - 9 * s ^ 6 - 1 := by ring
        rw [e]; have := pow_pos hs0 6; norm_num at h3 h4; linarith
      linarith
    set u := Real.sqrt (2 * f / A) with hu
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = 2 * f / A := Real.sq_sqrt (by positivity)
    have hu1 : u ≤ 1 := by
      rw [hu, Real.sqrt_le_one, div_le_one (by linarith)]; exact hc
    refine ⟨2 - u, by linarith, ?_⟩
    rw [phi_H m f u hu0 hu1]
    have hH : Hn m f u = 1 + m - 2 * f + 2 / 3 * f * u := by
      unfold Hn; rw [← hAdef]
      have : u ^ 3 = u * (2 * f / A) := by rw [← hu2]; ring
      rw [this]; field_simp; try ring
    rw [hH]
    set B := VNn m - (1 + m - 2 * f) with hB
    rcases le_total B 0 with hB0 | hB0
    · have : 0 ≤ 2 / 3 * f * u := by positivity
      linarith
    · have hlhs : 0 ≤ 2 / 3 * f * u := by positivity
      have hsq : B ^ 2 ≤ (2 / 3 * f * u) ^ 2 := by
        have e1 : (2 / 3 * f * u) ^ 2 = 8 * f ^ 3 * A / (9 * A ^ 2) := by
          rw [mul_pow, hu2]; field_simp; ring
        have hBA : B * A = m ^ 2 * (5 - 3 * m) - A * (1 + m - 2 * f) := by
          rw [hB]; unfold VNn; rw [← hAdef]; field_simp
        have e2 : B ^ 2 = 9 * (B * A) ^ 2 / (9 * A ^ 2) := by field_simp; try ring
        rw [e1, e2]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hid : 8 * f ^ 3 * A - 9 * (B * A) ^ 2 =
            (-59049) * s ^ 20 + 78732 * s ^ 19 + (-19683) * s ^ 18 + 39366 * s ^ 17 +
            (-65610) * s ^ 16 + 24057 * s ^ 15 + 2187 * s ^ 14 + 4374 * s ^ 13 + (-7290) * s ^ 12 +
            (-2916) * s ^ 11 + 3888 * s ^ 10 + 972 * s ^ 9 + (-243) * s ^ 8 + 162 * s ^ 7 +
            (-558) * s ^ 6 + 54 * s ^ 4 + 24 * s ^ 3 + (-1) := by
          rw [hBA, hAdef, hf, hm3]; ring
        have hP := PH_pos s hshalf hs1
        norm_num at hP
        linarith
      have := (pow_le_pow_iff_left₀ hB0 hlhs (by norm_num)).1 hsq
      linarith


theorem anal : ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧ ∀ m f : ℝ, 0 < m → m ≤ 1 → 0 ≤ f → f < 1 →
    gn f = m ^ 2 →
    (m ≤ ζ → ∃ q, 0 ≤ q ∧ VNn m ≤ phi m f q) ∧ (ζ < m → ∀ q, 0 ≤ q → phi m f q ≤ VNn m) := by
  obtain ⟨w0, hw0a, hw0b, hT0⟩ := Tp_root
  have hn1 : nfun 1 < nfun w0 := nfun_anti w0 1 (by linarith) (by linarith) le_rfl
  have hn0 : nfun w0 < nfun 0 := nfun_anti 0 w0 le_rfl (by linarith) (by linarith)
  have hn1v : nfun 1 = 1 / 3 := by unfold nfun; norm_num
  have hn0v : nfun 0 = 1 := by unfold nfun; norm_num
  set ζ := Real.sqrt (nfun w0) with hζ
  have hζ2 : ζ ^ 2 = nfun w0 := Real.sq_sqrt (by linarith)
  have hζ0 : 0 < ζ := Real.sqrt_pos.2 (by linarith)
  have hζ1 : ζ < 1 := by rw [hζ, Real.sqrt_lt' (by norm_num)]; norm_num; linarith
  refine ⟨ζ, hζ0, hζ1, ?_⟩
  intro m f hm0 hm1 hf0 hf1 hg
  have hA1 : 1 ≤ 1 + m - m ^ 2 := by
    have : 0 ≤ m * (1 - m) := mul_nonneg hm0.le (by linarith)
    have e : 1 + m - m ^ 2 = 1 + m * (1 - m) := by ring
    rw [e]; linarith
  unfold gn at hg
  split_ifs at hg with h2f
  · -- region II
    set w := Real.sqrt (2 * f) with hw
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hw2 : w ^ 2 = 2 * f := Real.sq_sqrt (by linarith)
    have hw1 : w ≤ 1 := by rw [hw, Real.sqrt_le_one]; linarith
    have hff : f = w ^ 2 / 2 := by linarith
    have hn : m ^ 2 = nfun w := by
      rw [← hg]; unfold nfun; rw [hff]; ring
    set r := Real.sqrt (1 + m - m ^ 2) with hr
    have hr2 : r ^ 2 = 1 + m - m ^ 2 := Real.sq_sqrt (by linarith)
    have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hA1
    have hr0 : 0 < r := by linarith
    set y := w / r with hy
    have hy0 : 0 ≤ y := by positivity
    have hy1 : y ≤ 1 := by rw [hy, div_le_one hr0]; linarith
    have hfy : f = (1 + m - m ^ 2) * y ^ 2 / 2 := by
      rw [hy, ← hr2, hff]; field_simp
    have hHy : Hn m f y = 1 + m - w ^ 2 + w ^ 3 / (3 * r) := by
      unfold Hn; rw [hy, ← hr2, hff]; field_simp; ring
    constructor
    · intro hmz
      have hww : w0 ≤ w := by
        by_contra h; push Not at h
        have := nfun_anti w w0 hw0 h (by linarith)
        have hm2 : m ^ 2 ≤ ζ ^ 2 := pow_le_pow_left₀ hm0.le hmz 2
        rw [hζ2, hn] at hm2; linarith
      have hwpos : 0 < w := by linarith
      have hT : 0 ≤ Tp w := by
        rcases eq_or_lt_of_le hww with h | h
        · rw [← h, hT0]
        · have := Tp_strictMono ⟨by linarith, by linarith⟩ ⟨hw0, hw1⟩ h
          linarith
      refine ⟨2 - y, by linarith, ?_⟩
      rw [phi_H m f y hy0 hy1, hHy]
      exact (regII_core m w r hwpos hw1 hm0 hm1 hn hr0 hr2).1 hT
    · intro hmz q hq
      have hle := regII_upper m f y hy0 hy1 hfy hA1 q hq
      rw [hHy] at hle
      refine le_trans hle ?_
      have hww : w < w0 := by
        by_contra h; push Not at h
        have h3 : nfun w ≤ nfun w0 := by
          rcases eq_or_lt_of_le h with h' | h'
          · rw [h']
          · exact (nfun_anti w0 w (by linarith) h' hw1).le
        have : ζ ^ 2 < m ^ 2 := pow_lt_pow_left₀ hmz hζ0.le (by norm_num)
        rw [hζ2, hn] at this; linarith
      rcases eq_or_lt_of_le hw0 with h | h
      · -- w = 0: then m = 1 and both sides equal 2
        rw [← h] at hn
        have hm : m = 1 := by
          have hn' : m ^ 2 = 1 := by rw [hn]; unfold nfun; norm_num
          have h2 : (m - 1) * (m + 1) = 0 := by linear_combination hn'
          rcases mul_eq_zero.1 h2 with h' | h'
          · linarith
          · linarith
        rw [← h, hm]; unfold VNn; norm_num
      · have hT : Tp w < 0 := by
          have := Tp_strictMono ⟨hw0, hw1⟩ ⟨by linarith, by linarith⟩ hww
          linarith
        exact (regII_core m w r h hw1 hm0 hm1 hn hr0 hr2).2 hT
  · -- region I
    push Not at h2f
    set z := Real.sqrt (2 - 2 * f) with hz
    have hz0 : 0 ≤ z := Real.sqrt_nonneg _
    have hz2 : z ^ 2 = 2 - 2 * f := Real.sq_sqrt (by linarith)
    have hz1 : z < 1 := by rw [hz, Real.sqrt_lt' (by norm_num)]; norm_num; linarith
    have hff : f = 1 - z ^ 2 / 2 := by linarith
    have hmz : m ^ 2 = z ^ 3 / 3 := by
      rw [← hg, hff]; ring
    have hzpos : 0 < z := by
      rcases eq_or_lt_of_le hz0 with h | h
      · rw [← h] at hmz
        have : 0 < m ^ 2 := by positivity
        norm_num at hmz; linarith
      · exact h
    have hmlt : m < ζ := by
      have : m ^ 2 < ζ ^ 2 := by
        rw [hζ2, hmz]
        have : z ^ 3 < 1 := by
          have := pow_lt_pow_left₀ hz1 hz0 (show (3:ℕ) ≠ 0 by norm_num); simpa using this
        linarith
      exact (pow_lt_pow_iff_left₀ hm0.le hζ0.le (by norm_num)).1 this
    constructor
    · intro _
      rw [hff]; exact regI m z hzpos hz1 hm0 hmz
    · intro h; exfalso; linarith

lemma phi_eq (m f q : ℝ) : phi m f q =
    (if q ≤ 1 then m ^ 2 + q * ((1 + m - m ^ 2) - f) - (1 + m - m ^ 2) * q ^ 3 / 6
     else if q ≤ 2 then 1 + m - 2 * f + f * (2 - q) - (1 + m - m ^ 2) * (2 - q) ^ 3 / 6
     else 1 + m - 2 * f - f * (q - 2)) := by
  unfold phi Ln Hn; split_ifs <;> ring

end FlexAnal

open FlexAnal in
theorem solution :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      ∀ m f : ℝ, 0 < m → m ≤ 1 → 0 ≤ f → f < 1 →
        (2 * f ≤ 1 → 2 / 3 * f * (Real.sqrt (2 * f) - 3) + 1 = m ^ 2) →
        (1 < 2 * f → 2 / 3 * (1 - f) * Real.sqrt (2 - 2 * f) = m ^ 2) →
        (m ≤ ζ → ∃ q : ℝ, 0 ≤ q ∧
          m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2) ≤
            (if q ≤ 1 then m ^ 2 + q * ((1 + m - m ^ 2) - f) - (1 + m - m ^ 2) * q ^ 3 / 6
             else if q ≤ 2 then 1 + m - 2 * f + f * (2 - q) - (1 + m - m ^ 2) * (2 - q) ^ 3 / 6
             else 1 + m - 2 * f - f * (q - 2))) ∧
        (ζ < m → ∀ q : ℝ, 0 ≤ q →
          (if q ≤ 1 then m ^ 2 + q * ((1 + m - m ^ 2) - f) - (1 + m - m ^ 2) * q ^ 3 / 6
           else if q ≤ 2 then 1 + m - 2 * f + f * (2 - q) - (1 + m - m ^ 2) * (2 - q) ^ 3 / 6
           else 1 + m - 2 * f - f * (q - 2)) ≤
            m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2)) := by
  obtain ⟨ζ, hζ0, hζ1, H⟩ := anal
  refine ⟨ζ, hζ0, hζ1, ?_⟩
  intro m f hm0 hm1 hf0 hf1 hg1 hg2
  have hg : gn f = m ^ 2 := by
    unfold gn; split_ifs with h
    · exact hg1 h
    · exact hg2 (by push Not at h; exact h)
  obtain ⟨Hlo, Hhi⟩ := H m f hm0 hm1 hf0 hf1 hg
  refine ⟨fun h => ?_, fun h q hq => ?_⟩
  · obtain ⟨q, hq, hv⟩ := Hlo h
    refine ⟨q, hq, ?_⟩
    rw [← phi_eq]; unfold VNn at hv; exact hv
  · rw [← phi_eq]; have := Hhi h q hq; unfold VNn at this; exact this

