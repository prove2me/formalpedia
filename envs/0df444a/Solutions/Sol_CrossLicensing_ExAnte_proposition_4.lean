-- Prove2me | solution 1 for CrossLicensing.ExAnte.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T21:44:26.397995+00:00
-- url     : https://prove2.me/submissions/70c4dd37-c809-428c-9bad-43cbe8952fce

import Mathlib
import Definitions.Def_CrossLicensing_ExAnte_Model

set_option autoImplicit false

namespace P607988be

open CrossLicensing.ExAnte

lemma s_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma s_lo : (1.732 : ℝ) < Real.sqrt 3 := by
  have h := s_sq
  have h0 := Real.sqrt_nonneg 3
  nlinarith

lemma s_hi : Real.sqrt 3 < (1.7321 : ℝ) := by
  have h := s_sq
  have h0 := Real.sqrt_nonneg 3
  nlinarith

/-- The supplier's optimum, once the duopoly vertex beats the monopoly vertex. -/
lemma opt_eq (β T1 T2 : ℝ) (hb : 0 < 1 + T2 + β * T1)
    (ha : (Real.sqrt 3 - 1) * (1 + T2 + β * T1) ≤ 1 + T1 + β * T2) :
    supplierOpt β T1 T2 = (2 + (1 + β) * (T1 + T2)) ^ 2 / 24 := by
  have hs := s_lo
  have hsq := s_sq
  have hr1 : r1 β T1 T2 = 2 * (1 + T1 + β * T2) - (1 + T2 + β * T1) := by
    simp only [r1]; ring
  have hr2 : r2 β T1 T2 = 1 + T2 + β * T1 := by simp only [r2]; ring
  have h75 : 5 * (1 + T2 + β * T1) ≤ 7 * (1 + T1 + β * T2) := by nlinarith
  have hsb : Real.sqrt 3 * (1 + T2 + β * T1) ≤ 2 + (1 + β) * (T1 + T2) := by nlinarith
  have h3 : 3 * (1 + T2 + β * T1) ^ 2 ≤ (2 + (1 + β) * (T1 + T2)) ^ 2 := by
    have h0 : 0 ≤ Real.sqrt 3 * (1 + T2 + β * T1) := by positivity
    have := mul_le_mul hsb hsb h0 (h0.trans hsb)
    nlinarith
  unfold supplierOpt
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨(2 + (1 + β) * (T1 + T2)) / 4, Set.mem_Ici.mpr ?_, ?_⟩
    · nlinarith
    · show supplierProfit β T1 T2 ((2 + (1 + β) * (T1 + T2)) / 4) = _
      have hc : (2 + (1 + β) * (T1 + T2)) / 4 ≤ r1 β T1 T2 := by rw [hr1]; nlinarith
      simp only [supplierProfit, q1, q2, if_pos hc]
      ring
  · rintro v ⟨r, hr, rfl⟩
    have hr0 : 0 ≤ r := hr
    show supplierProfit β T1 T2 r ≤ _
    simp only [supplierProfit, q1, q2]
    rw [hr1, hr2]
    split_ifs with h1 h2
    · nlinarith [sq_nonneg (2 + (1 + β) * (T1 + T2) - 4 * r)]
    · nlinarith [sq_nonneg (1 + T2 + β * T1 - 2 * r)]
    · nlinarith [sq_nonneg (2 + (1 + β) * (T1 + T2))]

/-- Denominator of khat2, sign-normalised. -/
noncomputable def QQ (k1 β : ℝ) : ℝ :=
  (7 - 4 * Real.sqrt 3) * ((1 - β) * (7 - 5 * β)) + 48 * (2 * Real.sqrt 3 - 3) * k1

lemma u_nonneg (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : 0 ≤ (1 - β) * (7 - 5 * β) := by
  apply mul_nonneg <;> linarith

lemma QQ_pos (k1 β : ℝ) (hk1 : 0 < k1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : 0 < QQ k1 β := by
  have hs := s_lo
  have hs2 := s_hi
  have hu := u_nonneg β hβ0 hβ1
  unfold QQ
  have h1 : 0 ≤ (7 - 4 * Real.sqrt 3) * ((1 - β) * (7 - 5 * β)) :=
    mul_nonneg (by linarith) hu
  have h2 : 0 < 48 * (2 * Real.sqrt 3 - 3) * k1 := by
    apply mul_pos _ hk1; nlinarith
  linarith

lemma khat_eq (k1 β : ℝ) (hk1 : 0 < k1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    khat2 k1 β = (4 * Real.sqrt 3 - 5) * ((1 - β) * (7 - 5 * β)) * k1 / QQ k1 β := by
  have hQ := QQ_pos k1 β hk1 hβ0 hβ1
  unfold khat2
  have hY : (4 * Real.sqrt 3 - 7) * (β - 1) * (5 * β - 7) + 48 * (3 - 2 * Real.sqrt 3) * k1
      = -QQ k1 β := by unfold QQ; ring
  rw [hY, div_eq_div_iff (neg_ne_zero.mpr hQ.ne') hQ.ne']
  ring

lemma khat_le_iff (k1 β k2 : ℝ) (hk1 : 0 < k1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    khat2 k1 β ≤ k2 ↔ (4 * Real.sqrt 3 - 5) * ((1 - β) * (7 - 5 * β)) * k1 ≤ k2 * QQ k1 β := by
  rw [khat_eq k1 β hk1 hβ0 hβ1, div_le_iff₀ (QQ_pos k1 β hk1 hβ0 hβ1)]

lemma lt_khat_iff (k1 β k2 : ℝ) (hk1 : 0 < k1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    k2 < khat2 k1 β ↔ k2 * QQ k1 β < (4 * Real.sqrt 3 - 5) * ((1 - β) * (7 - 5 * β)) * k1 := by
  rw [khat_eq k1 β hk1 hβ0 hβ1, lt_div_iff₀ (QQ_pos k1 β hk1 hβ0 hβ1)]

/-- In the interior region, `u ≤ 12 k2`. -/
lemma u_le_12k2 (k1 β k2 : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hk2 : 0 < k2) (h21 : k2 < k1)
    (hk : khat2 k1 β ≤ k2) : (1 - β) * (7 - 5 * β) ≤ 12 * k2 := by
  have hs := s_lo
  have hs2 := s_hi
  have hk1 : 0 < k1 := hk2.trans h21
  have h := (khat_le_iff k1 β k2 hk1 hβ0 hβ1).1 hk
  unfold QQ at h
  by_contra hc
  push Not at hc
  have hL : 0 < (4 * Real.sqrt 3 - 5) * k1 - (7 - 4 * Real.sqrt 3) * k2 := by
    nlinarith [mul_pos (show (0:ℝ) < 4 * Real.sqrt 3 - 5 by linarith) (sub_pos.mpr h21),
      mul_pos (show (0:ℝ) < 8 * Real.sqrt 3 - 12 by linarith) hk2]
  have e1 := mul_pos (sub_pos.mpr hc) hL
  have e2 := mul_pos (mul_pos hk2 (show (0:ℝ) < 7 - 4 * Real.sqrt 3 by linarith)) (sub_pos.mpr h21)
  nlinarith

/-- Interior denominator and numerator. -/
def DD (β k1 k2 : ℝ) : ℝ :=
  6 * (7 - 5 * β) ^ 2 * (k1 + k2) - 864 * k1 * k2 - (7 - 5 * β) * ((1 - β) * (7 - 5 * β)) * (1 + β)

def NN (β k1 k2 : ℝ) : ℝ := (1 - β) * (7 - 5 * β) * (k1 + k2) - 24 * k1 * k2

lemma DD_neg (β k1 k2 : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (h49 : 49 / 144 < k2) (h21 : k2 < k1)
    (hu : (1 - β) * (7 - 5 * β) ≤ 12 * k2) : DD β k1 k2 < 0 := by
  have hsplit : DD β k1 k2 = -864 * (k2 - (1 - β) * (7 - 5 * β) / 12) *
      (k2 - (7 - 5 * β) * (1 + β) / 72) + (k1 - k2) * (6 * (7 - 5 * β) ^ 2 - 864 * k2) := by
    unfold DD; ring
  have hc1 : (7 - 5 * β) * (1 + β) ≤ 14 := by nlinarith
  have hc2 : (7 - 5 * β) ^ 2 ≤ 49 := by nlinarith
  have e1 : 0 ≤ (k2 - (1 - β) * (7 - 5 * β) / 12) * (k2 - (7 - 5 * β) * (1 + β) / 72) := by
    apply mul_nonneg <;> linarith
  have e2 : 0 < (k1 - k2) * (864 * k2 - 6 * (7 - 5 * β) ^ 2) := by
    apply mul_pos <;> linarith
  rw [hsplit]; nlinarith

noncomputable def T1i (β k1 k2 : ℝ) : ℝ := (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k2) / DD β k1 k2
noncomputable def T2i (β k1 k2 : ℝ) : ℝ := (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k1) / DD β k1 k2

lemma interiorT_eq1 (β k1 k2 : ℝ) : interiorT β k1 k2 = T1i β k1 k2 := by
  unfold interiorT T1i DD; congr 1 <;> ring

lemma interiorT_eq2 (β k1 k2 : ℝ) : interiorT β k2 k1 = T2i β k1 k2 := by
  unfold interiorT T2i DD; congr 1 <;> ring

lemma interior_conds (k1 β k2 : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (h49 : 49 / 144 < k2)
    (h21 : k2 < k1) (hk : khat2 k1 β ≤ k2) :
    0 < 1 + T2i β k1 k2 + β * T1i β k1 k2 ∧
    (Real.sqrt 3 - 1) * (1 + T2i β k1 k2 + β * T1i β k1 k2) ≤ 1 + T1i β k1 k2 + β * T2i β k1 k2 ∧
    2 + (1 + β) * (T1i β k1 k2 + T2i β k1 k2) = 72 * NN β k1 k2 / DD β k1 k2 := by
  have hs := s_lo
  have hs2 := s_hi
  have hsq := s_sq
  have hk2 : 0 < k2 := by linarith
  have hk1 : 0 < k1 := by linarith
  have hu := u_le_12k2 k1 β k2 hβ0 hβ1 hk2 h21 hk
  have hD := DD_neg β k1 k2 hβ0 hβ1 h49 h21 hu
  have hDne : DD β k1 k2 ≠ 0 := hD.ne
  have hQk := (khat_le_iff k1 β k2 hk1 hβ0 hβ1).1 hk
  have hQ := QQ_pos k1 β hk1 hβ0 hβ1
  refine ⟨?_, ?_, ?_⟩
  · have e : 1 + T2i β k1 k2 + β * T1i β k1 k2 =
        (DD β k1 k2 + (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k1) +
          β * ((7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k2))) / DD β k1 k2 := by
      unfold T1i T2i; field_simp
    rw [e]
    apply div_pos_of_neg_of_neg _ hD
    have c0 : 0 < 7 - 5 * β := by linarith
    have f1 : (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k1) < 0 :=
      mul_neg_of_pos_of_neg c0 (by linarith)
    have f2 : 0 ≤ β * ((7 - 5 * β) * (12 * k2 - (1 - β) * (7 - 5 * β))) :=
      mul_nonneg hβ0 (mul_nonneg c0.le (by linarith))
    nlinarith
  · -- a - (s-1) b = M / D with M ≤ 0
    set s := Real.sqrt 3 with hs_def
    have e : 1 + T1i β k1 k2 + β * T2i β k1 k2 - (s - 1) * (1 + T2i β k1 k2 + β * T1i β k1 k2) =
        ((2 - s) * DD β k1 k2 +
          (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k2) * (1 - (s - 1) * β) +
          (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k1) * (β - (s - 1))) / DD β k1 k2 := by
      unfold T1i T2i; field_simp; ring
    have hm1 : (2 - s) * (6 * (7 - 5 * β) ^ 2 - 864 * k1) - 12 * (7 - 5 * β) * (1 - (s - 1) * β) < 0 := by
      have c2 : (7 - 5 * β) ^ 2 ≤ 49 := by nlinarith
      have g1 : (2 - s) * (6 * (7 - 5 * β) ^ 2 - 864 * k1) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by linarith)
      have g2 : 0 < 12 * (7 - 5 * β) * (1 - (s - 1) * β) :=
        mul_pos (by linarith) (by nlinarith)
      linarith
    have hMQ : ((2 - s) * DD β k1 k2 +
          (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k2) * (1 - (s - 1) * β) +
          (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k1) * (β - (s - 1))) * QQ k1 β =
        ((2 - s) * (6 * (7 - 5 * β) ^ 2 - 864 * k1) - 12 * (7 - 5 * β) * (1 - (s - 1) * β)) *
          (k2 * QQ k1 β - (4 * s - 5) * ((1 - β) * (7 - 5 * β)) * k1) := by
      unfold DD QQ
      rw [← hs_def]
      linear_combination (-1200 * β ^ 4 * k1 + 5760 * β ^ 3 * k1 + 2880 * β ^ 2 * k1 ^ 2
        - 10272 * β ^ 2 * k1 - 6912 * β * k1 ^ 2 + 8064 * β * k1 + 4032 * k1 ^ 2
        - 2352 * k1) * hsq
    have hM : ((2 - s) * DD β k1 k2 +
          (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k2) * (1 - (s - 1) * β) +
          (7 - 5 * β) * ((1 - β) * (7 - 5 * β) - 12 * k1) * (β - (s - 1))) ≤ 0 := by
      have hprod : ((2 - s) * (6 * (7 - 5 * β) ^ 2 - 864 * k1) - 12 * (7 - 5 * β) * (1 - (s - 1) * β)) *
          (k2 * QQ k1 β - (4 * s - 5) * ((1 - β) * (7 - 5 * β)) * k1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hm1.le (by linarith)
      rw [← hMQ] at hprod
      by_contra hc
      push Not at hc
      have := mul_pos hc hQ
      linarith
    have := div_nonneg_of_nonpos hM hD.le
    rw [← e] at this
    linarith
  · unfold T1i T2i NN
    field_simp
    unfold DD
    ring

/-- Profit in the interior region. -/
lemma eqP_in (k1 β k2 : ℝ) (hS : CrossLicensing.Innovation.Standing β k1 k2)
    (hk : khat2 k1 β ≤ k2) :
    equilibriumProfit k1 k2 β = (72 * NN β k1 k2 / DD β k1 k2) ^ 2 / 24 := by
  obtain ⟨hβ0, hβ1, h49, h21⟩ := hS
  obtain ⟨c1, c2, c3⟩ := interior_conds k1 β k2 hβ0 hβ1 h49 h21 hk
  unfold equilibriumProfit equilibriumT1 equilibriumT2
  rw [if_neg (not_lt.mpr hk), if_neg (not_lt.mpr hk), interiorT_eq1, interiorT_eq2,
    opt_eq β _ _ c1 c2, c3]

/-- In the boundary region, `β < 3/10` and the boundary denominator is positive. -/
lemma bd_facts (k1 β k2 : ℝ) (hS : CrossLicensing.Innovation.Standing β k1 k2)
    (hk : k2 < khat2 k1 β) : β < 3 / 10 ∧ 0 < boundaryDenom β k1 := by
  obtain ⟨hβ0, hβ1, h49, h21⟩ := hS
  have hs := s_lo
  have hs2 := s_hi
  have hk1 : 0 < k1 := by linarith
  have h := (lt_khat_iff k1 β k2 hk1 hβ0 hβ1).1 hk
  have hQ := QQ_pos k1 β hk1 hβ0 hβ1
  have hu := u_nonneg β hβ0 hβ1
  have hb : β < 3 / 10 := by
    by_contra hc
    push Not at hc
    have hu2 : (1 - β) * (7 - 5 * β) ≤ 77 / 20 := by nlinarith
    have g1 : 49 / 144 * QQ k1 β < k2 * QQ k1 β := mul_lt_mul_of_pos_right h49 hQ
    have g2 : 49 / 144 * (48 * (2 * Real.sqrt 3 - 3) * k1) ≤ 49 / 144 * QQ k1 β := by
      unfold QQ
      have : 0 ≤ (7 - 4 * Real.sqrt 3) * ((1 - β) * (7 - 5 * β)) := mul_nonneg (by linarith) hu
      linarith
    have g3 : (4 * Real.sqrt 3 - 5) * ((1 - β) * (7 - 5 * β)) * k1 ≤
        (4 * Real.sqrt 3 - 5) * (77 / 20) * k1 := by
      apply mul_le_mul_of_nonneg_right _ hk1.le
      apply mul_le_mul_of_nonneg_left hu2; linarith
    have g4 : (4 * Real.sqrt 3 - 5) * (77 / 20) * k1 < 49 / 144 * (48 * (2 * Real.sqrt 3 - 3) * k1) := by
      have : (4 * Real.sqrt 3 - 5) * (77 / 20) < 49 / 144 * (48 * (2 * Real.sqrt 3 - 3)) := by
        nlinarith
      nlinarith
    linarith
  refine ⟨hb, ?_⟩
  unfold boundaryDenom
  have e : (4 * Real.sqrt 3 - 7) * (β - 1) * (β + 1) * (5 * β - 7) -
      48 * (Real.sqrt 3 * β + Real.sqrt 3 - 3) * k1 =
      48 * (3 - Real.sqrt 3 * (1 + β)) * k1 -
        (7 - 4 * Real.sqrt 3) * ((1 + β) * ((1 - β) * (7 - 5 * β))) := by ring
  rw [e]
  have f1 : (1 + β) * ((1 - β) * (7 - 5 * β)) ≤ 10 := by nlinarith
  have f2 : 0 ≤ (1 + β) * ((1 - β) * (7 - 5 * β)) := mul_nonneg (by linarith) hu
  have f3 : (7 - 4 * Real.sqrt 3) * ((1 + β) * ((1 - β) * (7 - 5 * β))) ≤ (7 - 4 * Real.sqrt 3) * 10 :=
    mul_le_mul_of_nonneg_left f1 (by linarith)
  have f4 : 0.7 * k1 ≤ (3 - Real.sqrt 3 * (1 + β)) * k1 := by
    apply mul_le_mul_of_nonneg_right _ hk1.le; nlinarith
  nlinarith

/-- Profit in the boundary region. -/
lemma eqP_bd (k1 β k2 : ℝ) (hS : CrossLicensing.Innovation.Standing β k1 k2)
    (hk : k2 < khat2 k1 β) :
    equilibriumProfit k1 k2 β = (144 * k1 * (1 - β) / boundaryDenom β k1) ^ 2 / 24 := by
  obtain ⟨hb3, hB⟩ := bd_facts k1 β k2 hS hk
  obtain ⟨hβ0, hβ1, h49, h21⟩ := hS
  have hs := s_lo
  have hsq := s_sq
  have hk1 : 0 < k1 := by linarith
  have hBne := hB.ne'
  have eb : 1 + boundaryT2 β k1 + β * boundaryT1 β k1 =
      48 * Real.sqrt 3 * k1 * (1 - β) / boundaryDenom β k1 := by
    unfold boundaryT1 boundaryT2
    field_simp
    unfold boundaryDenom
    ring
  have ea : 1 + boundaryT1 β k1 + β * boundaryT2 β k1 =
      48 * (3 - Real.sqrt 3) * k1 * (1 - β) / boundaryDenom β k1 := by
    unfold boundaryT1 boundaryT2
    field_simp
    unfold boundaryDenom
    ring
  have c1 : 0 < 1 + boundaryT2 β k1 + β * boundaryT1 β k1 := by
    rw [eb]; apply div_pos _ hB
    apply mul_pos (mul_pos (by linarith) hk1) (by linarith)
  have c2 : (Real.sqrt 3 - 1) * (1 + boundaryT2 β k1 + β * boundaryT1 β k1) ≤
      1 + boundaryT1 β k1 + β * boundaryT2 β k1 := by
    rw [ea, eb, mul_div_assoc']
    apply le_of_eq
    congr 1
    linear_combination (48 * k1 * (1 - β)) * hsq
  have c3 : 2 + (1 + β) * (boundaryT1 β k1 + boundaryT2 β k1) =
      144 * k1 * (1 - β) / boundaryDenom β k1 := by
    have : 2 + (1 + β) * (boundaryT1 β k1 + boundaryT2 β k1) =
        (1 + boundaryT1 β k1 + β * boundaryT2 β k1) + (1 + boundaryT2 β k1 + β * boundaryT1 β k1) := by
      ring
    rw [this, ea, eb, ← add_div]
    congr 1; ring
  unfold equilibriumProfit equilibriumT1 equilibriumT2
  rw [if_pos hk, if_pos hk, opt_eq β _ _ c1 c2, c3]

/-- Threshold lemmas. -/
lemma down_thr (R : Set ℝ) (Pr : ℝ → Prop) (f : ℝ → ℝ) (L U : ℝ) (hf : Continuous f)
    (hR : ∀ x ∈ R, L < x ∧ x < U) (hP : ∀ x ∈ R, (Pr x ↔ 0 ≤ f x))
    (hdown : ∀ x ∈ R, ∀ y ∈ R, x ≤ y → Pr y → Pr x) :
    ∃ t : ℝ, ∀ x ∈ R, (Pr x ↔ x ≤ t) := by
  by_cases hne : ∃ x ∈ R, Pr x
  · let S := {x | x ∈ R ∧ Pr x}
    have hSne : S.Nonempty := by obtain ⟨x, hx, hp⟩ := hne; exact ⟨x, hx, hp⟩
    have hSbdd : BddAbove S := ⟨U, fun x hx => (hR x hx.1).2.le⟩
    refine ⟨sSup S, fun x hx => ⟨fun hp => le_csSup hSbdd ⟨hx, hp⟩, fun hle => ?_⟩⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup hSne hlt
      exact hdown x hx y hy.1 hxy.le hy.2
    · have hcl : sSup S ∈ closure S := csSup_mem_closure hSne hSbdd
      have hsub : S ⊆ {y | 0 ≤ f y} := fun y hy => (hP y hy.1).1 hy.2
      have hclosed : IsClosed {y | 0 ≤ f y} := isClosed_le continuous_const hf
      have hmem : sSup S ∈ {y | 0 ≤ f y} := (closure_minimal hsub hclosed) hcl
      rw [hP x hx, heq]; exact hmem
  · push Not at hne
    exact ⟨L, fun x hx => ⟨fun hp => absurd hp (hne x hx),
      fun hle => absurd hle (not_le.mpr (hR x hx).1)⟩⟩

lemma up_thr (R : Set ℝ) (Pr : ℝ → Prop) (f : ℝ → ℝ) (L U : ℝ) (hf : Continuous f)
    (hR : ∀ x ∈ R, L < x ∧ x < U) (hP : ∀ x ∈ R, (Pr x ↔ 0 ≤ f x))
    (hup : ∀ x ∈ R, ∀ y ∈ R, x ≤ y → Pr x → Pr y) :
    ∃ t : ℝ, ∀ x ∈ R, (Pr x ↔ t ≤ x) := by
  by_cases hne : ∃ x ∈ R, Pr x
  · let S := {x | x ∈ R ∧ Pr x}
    have hSne : S.Nonempty := by obtain ⟨x, hx, hp⟩ := hne; exact ⟨x, hx, hp⟩
    have hSbdd : BddBelow S := ⟨L, fun x hx => (hR x hx.1).1.le⟩
    refine ⟨sInf S, fun x hx => ⟨fun hp => csInf_le hSbdd ⟨hx, hp⟩, fun hle => ?_⟩⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨y, hy, hxy⟩ := exists_lt_of_csInf_lt hSne hlt
      exact hup y hy.1 x hx hxy.le hy.2
    · have hcl : sInf S ∈ closure S := csInf_mem_closure hSne hSbdd
      have hsub : S ⊆ {y | 0 ≤ f y} := fun y hy => (hP y hy.1).1 hy.2
      have hclosed : IsClosed {y | 0 ≤ f y} := isClosed_le continuous_const hf
      have hmem : sInf S ∈ {y | 0 ≤ f y} := (closure_minimal hsub hclosed) hcl
      rw [hP x hx, ← heq]; exact hmem
  · push Not at hne
    exact ⟨U, fun x hx => ⟨fun hp => absurd hp (hne x hx),
      fun hle => absurd hle (not_le.mpr (hR x hx).2)⟩⟩


lemma standing0 {β k1 k2 : ℝ} (hS : CrossLicensing.Innovation.Standing β k1 k2) :
    CrossLicensing.Innovation.Standing 0 k1 k2 :=
  ⟨le_rfl, zero_le_one, hS.2.2.1, hS.2.2.2⟩

lemma sq24_iff (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x ^ 2 / 24 ≤ y ^ 2 / 24 ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_left hc (by linarith : (0:ℝ) < x + y)]
  · intro h
    nlinarith [mul_le_mul h h hx (hx.trans h)]

lemma nonneg_div_pos_iff (a p : ℝ) (hp : 0 < p) : 0 ≤ a / p ↔ 0 ≤ a :=
  ⟨fun h => by
    have := mul_nonneg h hp.le
    rwa [div_mul_cancel₀ a hp.ne'] at this, fun h => div_nonneg h hp.le⟩

lemma khat_strictAnti (k1 : ℝ) (hk1 : 0 < k1) :
    StrictAntiOn (fun β' : ℝ => khat2 k1 β') (Set.Icc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  show khat2 k1 y < khat2 k1 x
  have hs := s_lo
  have hs2 := s_hi
  rw [khat_eq k1 x hk1 hx0 hx1, khat_eq k1 y hk1 hy0 hy1,
    div_lt_div_iff₀ (QQ_pos k1 y hk1 hy0 hy1) (QQ_pos k1 x hk1 hx0 hx1)]
  have hu : (1 - y) * (7 - 5 * y) < (1 - x) * (7 - 5 * x) := by
    nlinarith [mul_pos (sub_pos.mpr hxy) (show (0:ℝ) < 12 - 5 * (x + y) by linarith)]
  have e : (4 * Real.sqrt 3 - 5) * ((1 - y) * (7 - 5 * y)) * k1 * QQ k1 x -
      (4 * Real.sqrt 3 - 5) * ((1 - x) * (7 - 5 * x)) * k1 * QQ k1 y =
      (4 * Real.sqrt 3 - 5) * k1 * (48 * (2 * Real.sqrt 3 - 3) * k1) *
        ((1 - y) * (7 - 5 * y) - (1 - x) * (7 - 5 * x)) := by
    unfold QQ; ring
  have hp : 0 < (4 * Real.sqrt 3 - 5) * k1 * (48 * (2 * Real.sqrt 3 - 3) * k1) := by
    apply mul_pos (mul_pos (by linarith) hk1) (mul_pos (by linarith) hk1)
  have := mul_neg_of_pos_of_neg hp (sub_neg.mpr hu)
  linarith

lemma NN_neg (β k1 k2 : ℝ) (hk2 : 0 < k2) (h21 : k2 < k1)
    (hu : (1 - β) * (7 - 5 * β) ≤ 12 * k2) : NN β k1 k2 < 0 := by
  unfold NN
  have hk1 : 0 < k1 := hk2.trans h21
  nlinarith [mul_le_mul_of_nonneg_right hu (hk1.le), mul_le_mul_of_nonneg_right hu (hk2.le),
    mul_pos hk2 (sub_pos.mpr h21)]

lemma G_pos (β k1 k2 : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (h49 : 49 / 144 < k2) (h21 : k2 < k1)
    (hu : (1 - β) * (7 - 5 * β) ≤ 12 * k2) : 0 < 72 * NN β k1 k2 / DD β k1 k2 :=
  div_pos_of_neg_of_neg (by have := NN_neg β k1 k2 (by linarith) h21 hu; linarith)
    (DD_neg β k1 k2 hβ0 hβ1 h49 h21 hu)

lemma G_anti (β k1 x y : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx : DD β k1 x < 0) (hy : DD β k1 y < 0)
    (hxy : x ≤ y) : 72 * NN β k1 y / DD β k1 y ≤ 72 * NN β k1 x / DD β k1 x := by
  rw [← sub_nonneg, div_sub_div _ _ hx.ne hy.ne]
  apply div_nonneg _ (mul_pos_of_neg_of_neg hx hy).le
  have key : 72 * NN β k1 x * DD β k1 y - DD β k1 x * (72 * NN β k1 y) =
      72 * ((y - x) * ((7 - 5 * β) * (1 + β) * (12 * k1 - (1 - β) * (7 - 5 * β)) ^ 2)) := by
    unfold NN DD; ring
  rw [key]
  apply mul_nonneg (by norm_num)
  apply mul_nonneg (by linarith)
  apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)

lemma bden0_pos (k1 : ℝ) (hk1 : 49 / 144 < k1) : 0 < boundaryDenom 0 k1 := by
  have hs := s_lo
  have hs2 := s_hi
  unfold boundaryDenom
  nlinarith [mul_pos (show (0:ℝ) < 3 - Real.sqrt 3 by linarith) (show (0:ℝ) < k1 by linarith)]

/-- The comparison polynomial for the interior/interior region. -/
lemma q_eq (β k1 k : ℝ) :
    72 * NN β k1 k * DD 0 k1 k - DD β k1 k * (72 * NN 0 k1 k) =
    72 * (β * ((2 - 5 * β) * (7 * β * (12 - 5 * β) * ((k1 - 7 / 12) + (k - 7 / 12)) +
      144 * (k1 - 7 / 12) * (k - 7 / 12) * ((k1 - 7 / 12) + (k - 7 / 12)) +
      24 * (7 + 12 * β - 5 * β ^ 2) * (k1 - 7 / 12) * (k - 7 / 12)) -
      420 * ((k1 - 7 / 12) - (k - 7 / 12)) ^ 2)) := by
  unfold NN DD; ring

lemma qt_neg (β X Y : ℝ) (hb : 2 / 5 ≤ β) (hβ1 : β ≤ 1) (hY : 0 ≤ Y) (hXY : Y < X) :
    (2 - 5 * β) * (7 * β * (12 - 5 * β) * (X + Y) + 144 * X * Y * (X + Y) +
      24 * (7 + 12 * β - 5 * β ^ 2) * X * Y) - 420 * (X - Y) ^ 2 < 0 := by
  have hX : 0 < X := by linarith
  have h1 : 0 ≤ 7 * β * (12 - 5 * β) * (X + Y) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h2 : 0 ≤ 144 * X * Y * (X + Y) := by positivity
  have h3 : 0 ≤ 24 * (7 + 12 * β - 5 * β ^ 2) * X * Y := by
    have : 0 ≤ 7 + 12 * β - 5 * β ^ 2 := by nlinarith
    positivity
  have h4 : (2 - 5 * β) * (7 * β * (12 - 5 * β) * (X + Y) + 144 * X * Y * (X + Y) +
      24 * (7 + 12 * β - 5 * β ^ 2) * X * Y) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have h5 : 0 < (X - Y) ^ 2 := pow_pos (by linarith) 2
  linarith

lemma qt_mono (β X Y Y' : ℝ) (hb0 : 0 ≤ β) (hb : β < 2 / 5) (hY' : 0 ≤ Y') (hYY : Y' ≤ Y)
    (hYX : Y ≤ X) :
    (2 - 5 * β) * (7 * β * (12 - 5 * β) * (X + Y') + 144 * X * Y' * (X + Y') +
      24 * (7 + 12 * β - 5 * β ^ 2) * X * Y') - 420 * (X - Y') ^ 2 ≤
    (2 - 5 * β) * (7 * β * (12 - 5 * β) * (X + Y) + 144 * X * Y * (X + Y) +
      24 * (7 + 12 * β - 5 * β ^ 2) * X * Y) - 420 * (X - Y) ^ 2 := by
  rw [← sub_nonneg]
  have e : ((2 - 5 * β) * (7 * β * (12 - 5 * β) * (X + Y) + 144 * X * Y * (X + Y) +
      24 * (7 + 12 * β - 5 * β ^ 2) * X * Y) - 420 * (X - Y) ^ 2) -
      ((2 - 5 * β) * (7 * β * (12 - 5 * β) * (X + Y') + 144 * X * Y' * (X + Y') +
      24 * (7 + 12 * β - 5 * β ^ 2) * X * Y') - 420 * (X - Y') ^ 2) =
      (Y - Y') * ((2 - 5 * β) * (7 * β * (12 - 5 * β) + 144 * X * (X + Y + Y') +
        24 * (7 + 12 * β - 5 * β ^ 2) * X) + 420 * (2 * X - Y - Y')) := by ring
  rw [e]
  have hX : 0 ≤ X := by linarith
  have h7 : 0 ≤ 7 + 12 * β - 5 * β ^ 2 := by nlinarith
  apply mul_nonneg (by linarith)
  have : 0 ≤ (2 - 5 * β) * (7 * β * (12 - 5 * β) + 144 * X * (X + Y + Y') +
        24 * (7 + 12 * β - 5 * β ^ 2) * X) := by
    apply mul_nonneg (by linarith)
    have a1 : 0 ≤ 7 * β * (12 - 5 * β) := mul_nonneg (by linarith) (by linarith)
    have a2 : 0 ≤ 144 * X * (X + Y + Y') := by
      apply mul_nonneg (by linarith); linarith
    have a3 : 0 ≤ 24 * (7 + 12 * β - 5 * β ^ 2) * X := by positivity
    linarith
  linarith

end P607988be

open CrossLicensing.ExAnte in
theorem solution (k1 β : ℝ)
    (hk1 : (49 : ℝ) / 144 < k1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∀ k2 : ℝ, CrossLicensing.Innovation.Standing β k1 k2 → k2 < khat2 k1 β →
      k2 < khat2 k1 0 ∧
      equilibriumProfit k1 k2 0 ≤ equilibriumProfit k1 k2 β) ∧
    StrictAntiOn (fun β' : ℝ => khat2 k1 β') (Set.Icc 0 1) ∧
    khat2 k1 1 = 0 ∧
    (∃ βbar : ℝ, 0 ≤ βbar ∧ βbar < 1 ∧
      ∀ β' : ℝ, βbar ≤ β' → β' ≤ 1 →
        ∀ k2 : ℝ, CrossLicensing.Innovation.Standing β' k1 k2 → ¬ k2 < khat2 k1 β') ∧
    (∃ ktilde : ℝ, ∀ k2 : ℝ, CrossLicensing.Innovation.Standing β k1 k2 →
      khat2 k1 β ≤ k2 → k2 < khat2 k1 0 →
        (equilibriumProfit k1 k2 0 ≤ equilibriumProfit k1 k2 β ↔ k2 ≤ ktilde)) ∧
    (∃ kunder : ℝ, ∀ k2 : ℝ, CrossLicensing.Innovation.Standing β k1 k2 →
      khat2 k1 0 ≤ k2 →
        (equilibriumProfit k1 k2 0 ≤ equilibriumProfit k1 k2 β ↔ kunder ≤ k2)) ∧
    ((2 : ℝ) / 5 ≤ β → ∀ k2 : ℝ, CrossLicensing.Innovation.Standing β k1 k2 →
      khat2 k1 0 ≤ k2 →
        equilibriumProfit k1 k2 β ≤ equilibriumProfit k1 k2 0) := by
  have hk1p : 0 < k1 := by linarith
  have hs := P607988be.s_lo
  have hs2 := P607988be.s_hi
  have hanti := P607988be.khat_strictAnti k1 hk1p
  have hkk0 : khat2 k1 β ≤ khat2 k1 0 := by
    rcases eq_or_lt_of_le hβ0 with h | h
    · rw [← h]
    · exact (hanti ⟨le_rfl, zero_le_one⟩ ⟨hβ0, hβ1⟩ h).le
  -- the interior/interior comparison, shared by the last two parts
  have hII : ∀ k : ℝ, CrossLicensing.Innovation.Standing β k1 k → khat2 k1 0 ≤ k →
      (7 / 12 ≤ k ∧ k < k1) ∧
      (equilibriumProfit k1 k 0 ≤ equilibriumProfit k1 k β ↔
        0 ≤ 72 * P607988be.NN β k1 k * P607988be.DD 0 k1 k - P607988be.DD β k1 k * (72 * P607988be.NN 0 k1 k)) ∧
      (equilibriumProfit k1 k β ≤ equilibriumProfit k1 k 0 ↔
        0 ≤ -(72 * P607988be.NN β k1 k * P607988be.DD 0 k1 k - P607988be.DD β k1 k * (72 * P607988be.NN 0 k1 k))) := by
    intro k hS hk0
    have hS0 := P607988be.standing0 hS
    obtain ⟨_, _, h49, h21⟩ := hS
    have hkb : khat2 k1 β ≤ k := hkk0.trans hk0
    have hu0 := P607988be.u_le_12k2 k1 0 k le_rfl zero_le_one (by linarith) h21 hk0
    have hub := P607988be.u_le_12k2 k1 β k hβ0 hβ1 (by linarith) h21 hkb
    have hD0 := P607988be.DD_neg 0 k1 k le_rfl zero_le_one h49 h21 hu0
    have hDb := P607988be.DD_neg β k1 k hβ0 hβ1 h49 h21 hub
    have hG0 := P607988be.G_pos 0 k1 k le_rfl zero_le_one h49 h21 hu0
    have hGb := P607988be.G_pos β k1 k hβ0 hβ1 h49 h21 hub
    refine ⟨⟨by linarith, h21⟩, ?_, ?_⟩
    · rw [P607988be.eqP_in k1 0 k hS0 hk0, P607988be.eqP_in k1 β k ⟨hβ0, hβ1, h49, h21⟩ hkb,
        P607988be.sq24_iff _ _ hG0.le hGb.le, ← sub_nonneg, div_sub_div _ _ hDb.ne hD0.ne,
        P607988be.nonneg_div_pos_iff _ _ (mul_pos_of_neg_of_neg hDb hD0)]
    · rw [P607988be.eqP_in k1 0 k hS0 hk0, P607988be.eqP_in k1 β k ⟨hβ0, hβ1, h49, h21⟩ hkb,
        P607988be.sq24_iff _ _ hGb.le hG0.le, ← sub_nonneg, div_sub_div _ _ hD0.ne hDb.ne,
        P607988be.nonneg_div_pos_iff _ _ (mul_pos_of_neg_of_neg hD0 hDb)]
      rw [show 72 * P607988be.NN 0 k1 k * P607988be.DD β k1 k - P607988be.DD 0 k1 k * (72 * P607988be.NN β k1 k) =
        -(72 * P607988be.NN β k1 k * P607988be.DD 0 k1 k - P607988be.DD β k1 k * (72 * P607988be.NN 0 k1 k)) by ring]
  refine ⟨?_, hanti, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) boundary region
    intro k2 hS hk
    have hk0 : k2 < khat2 k1 0 := lt_of_lt_of_le hk hkk0
    refine ⟨hk0, ?_⟩
    have hS0 := P607988be.standing0 hS
    obtain ⟨_, hB⟩ := P607988be.bd_facts k1 β k2 hS hk
    obtain ⟨_, hB0⟩ := P607988be.bd_facts k1 0 k2 hS0 hk0
    rw [P607988be.eqP_bd k1 β k2 hS hk, P607988be.eqP_bd k1 0 k2 hS0 hk0]
    have h0 : 0 ≤ 144 * k1 * (1 - 0) / boundaryDenom 0 k1 :=
      div_nonneg (by linarith) hB0.le
    have hle : 144 * k1 * (1 - 0) / boundaryDenom 0 k1 ≤
        144 * k1 * (1 - β) / boundaryDenom β k1 := by
      rw [div_le_div_iff₀ hB0 hB]
      have e : 144 * k1 * (1 - β) * boundaryDenom 0 k1 - 144 * k1 * (1 - 0) * boundaryDenom β k1
          = 144 * k1 * (β * ((4 * Real.sqrt 3 - 7) * ((1 - β) * (5 * β - 2)) +
            48 * (2 * Real.sqrt 3 - 3) * k1)) := by
        unfold boundaryDenom; ring
      have t1 : -2 ≤ (1 - β) * (5 * β - 2) := by nlinarith
      have t2 : (1 - β) * (5 * β - 2) ≤ 1 := by nlinarith
      have t3 : -1 ≤ (4 * Real.sqrt 3 - 7) * ((1 - β) * (5 * β - 2)) := by
        nlinarith [mul_nonneg (show (0:ℝ) ≤ 7 - 4 * Real.sqrt 3 by linarith)
          (show (0:ℝ) ≤ 1 - (1 - β) * (5 * β - 2) by linarith)]
      have t4 : 1 ≤ 48 * (2 * Real.sqrt 3 - 3) * k1 := by
        nlinarith [mul_pos (show (0:ℝ) < 2 * Real.sqrt 3 - 3 - 0.46 by linarith)
          (show (0:ℝ) < k1 by linarith)]
      have := mul_nonneg (show (0:ℝ) ≤ 144 * k1 by linarith) (mul_nonneg hβ0 (by linarith : (0:ℝ) ≤
        (4 * Real.sqrt 3 - 7) * ((1 - β) * (5 * β - 2)) + 48 * (2 * Real.sqrt 3 - 3) * k1))
      linarith
    exact (P607988be.sq24_iff _ _ h0 (h0.trans hle)).2 hle
  · -- khat2 vanishes at β = 1
    unfold khat2; simp
  · -- no boundary region near β = 1
    refine ⟨1 / 2, by norm_num, by norm_num, fun β' h1 h2 k2 hS hlt => ?_⟩
    have hβ'0 : 0 ≤ β' := by linarith
    have hk := (P607988be.lt_khat_iff k1 β' k2 hk1p hβ'0 h2).1 hlt
    obtain ⟨_, _, h49, _⟩ := hS
    have hu2 : (1 - β') * (7 - 5 * β') ≤ 9 / 4 := by nlinarith
    have hu0 := P607988be.u_nonneg β' hβ'0 h2
    have hQ := P607988be.QQ_pos k1 β' hk1p hβ'0 h2
    have g1 : 49 / 144 * P607988be.QQ k1 β' < k2 * P607988be.QQ k1 β' := mul_lt_mul_of_pos_right h49 hQ
    have g2 : 49 / 144 * (48 * (2 * Real.sqrt 3 - 3) * k1) ≤ 49 / 144 * P607988be.QQ k1 β' := by
      unfold P607988be.QQ
      nlinarith [mul_nonneg (show (0:ℝ) ≤ 7 - 4 * Real.sqrt 3 by linarith) hu0]
    have g3 : (4 * Real.sqrt 3 - 5) * ((1 - β') * (7 - 5 * β')) * k1 ≤
        (4 * Real.sqrt 3 - 5) * (9 / 4) * k1 := by
      apply mul_le_mul_of_nonneg_right _ hk1p.le
      apply mul_le_mul_of_nonneg_left hu2; linarith
    have g4 : (4 * Real.sqrt 3 - 5) * (9 / 4) * k1 < 49 / 144 * (48 * (2 * Real.sqrt 3 - 3) * k1) := by
      have : (4 * Real.sqrt 3 - 5) * (9 / 4) < 49 / 144 * (48 * (2 * Real.sqrt 3 - 3)) := by
        nlinarith
      nlinarith
    linarith
  · -- (ii) interior with licensing, boundary without
    have hB0 := P607988be.bden0_pos k1 hk1
    let R : Set ℝ := {k | CrossLicensing.Innovation.Standing β k1 k ∧ khat2 k1 β ≤ k ∧
      k < khat2 k1 0}
    have hRb : ∀ k ∈ R, 49 / 144 < k ∧ k < k1 := fun k hk => ⟨hk.1.2.2.1, hk.1.2.2.2⟩
    have hPG : ∀ k ∈ R, (equilibriumProfit k1 k 0 ≤ equilibriumProfit k1 k β ↔
        144 * k1 * (1 - 0) / boundaryDenom 0 k1 ≤ 72 * P607988be.NN β k1 k / P607988be.DD β k1 k) := by
      intro k hk
      obtain ⟨hS, hkb, hk0⟩ := hk
      have h49 := hS.2.2.1
      have h21 := hS.2.2.2
      have hub := P607988be.u_le_12k2 k1 β k hβ0 hβ1 (by linarith) h21 hkb
      have hGb := P607988be.G_pos β k1 k hβ0 hβ1 h49 h21 hub
      rw [P607988be.eqP_bd k1 0 k (P607988be.standing0 hS) hk0, P607988be.eqP_in k1 β k hS hkb,
        P607988be.sq24_iff _ _ (div_nonneg (by linarith) hB0.le) hGb.le]
    have hP : ∀ k ∈ R, (equilibriumProfit k1 k 0 ≤ equilibriumProfit k1 k β ↔
        0 ≤ 144 * k1 * P607988be.DD β k1 k - 72 * P607988be.NN β k1 k * boundaryDenom 0 k1) := by
      intro k hk
      rw [hPG k hk]
      obtain ⟨hS, hkb, hk0⟩ := hk
      obtain ⟨_, _, h49, h21⟩ := hS
      have hub := P607988be.u_le_12k2 k1 β k hβ0 hβ1 (by linarith) h21 hkb
      have hDb := P607988be.DD_neg β k1 k hβ0 hβ1 h49 h21 hub
      have hDne := hDb.ne
      have hBne := hB0.ne'
      have e : 72 * P607988be.NN β k1 k / P607988be.DD β k1 k - 144 * k1 * (1 - 0) / boundaryDenom 0 k1 =
          (144 * k1 * P607988be.DD β k1 k - 72 * P607988be.NN β k1 k * boundaryDenom 0 k1) /
            (-(P607988be.DD β k1 k) * boundaryDenom 0 k1) := by
        field_simp
        ring
      rw [← sub_nonneg, e, P607988be.nonneg_div_pos_iff _ _ (mul_pos (by linarith) hB0)]
    have hdown : ∀ x ∈ R, ∀ y ∈ R, x ≤ y →
        (equilibriumProfit k1 y 0 ≤ equilibriumProfit k1 y β) →
        (equilibriumProfit k1 x 0 ≤ equilibriumProfit k1 x β) := by
      intro x hx y hy hxy hPy
      rw [hPG x hx]
      rw [hPG y hy] at hPy
      obtain ⟨⟨_, _, hx49, hx21⟩, hxb, _⟩ := hx
      obtain ⟨⟨_, _, hy49, hy21⟩, hyb, _⟩ := hy
      have hux := P607988be.u_le_12k2 k1 β x hβ0 hβ1 (by linarith) hx21 hxb
      have huy := P607988be.u_le_12k2 k1 β y hβ0 hβ1 (by linarith) hy21 hyb
      exact hPy.trans (P607988be.G_anti β k1 x y hβ0 hβ1 (P607988be.DD_neg β k1 x hβ0 hβ1 hx49 hx21 hux)
        (P607988be.DD_neg β k1 y hβ0 hβ1 hy49 hy21 huy) hxy)
    have hf : Continuous (fun k : ℝ => 144 * k1 * P607988be.DD β k1 k - 72 * P607988be.NN β k1 k * boundaryDenom 0 k1) := by
      unfold P607988be.DD P607988be.NN; fun_prop
    obtain ⟨t, ht⟩ := P607988be.down_thr R (fun k => equilibriumProfit k1 k 0 ≤ equilibriumProfit k1 k β)
      _ (49 / 144) k1 hf hRb hP hdown
    exact ⟨t, fun k2 hS h1 h2 => ht k2 ⟨hS, h1, h2⟩⟩
  · -- (iii) interior in both
    let R : Set ℝ := {k | CrossLicensing.Innovation.Standing β k1 k ∧ khat2 k1 0 ≤ k}
    have hRb : ∀ k ∈ R, 49 / 144 < k ∧ k < k1 := fun k hk => ⟨hk.1.2.2.1, hk.1.2.2.2⟩
    have hP : ∀ k ∈ R, (equilibriumProfit k1 k 0 ≤ equilibriumProfit k1 k β ↔
        0 ≤ 72 * P607988be.NN β k1 k * P607988be.DD 0 k1 k - P607988be.DD β k1 k * (72 * P607988be.NN 0 k1 k)) :=
      fun k hk => (hII k hk.1 hk.2).2.1
    have hup : ∀ x ∈ R, ∀ y ∈ R, x ≤ y →
        (equilibriumProfit k1 x 0 ≤ equilibriumProfit k1 x β) →
        (equilibriumProfit k1 y 0 ≤ equilibriumProfit k1 y β) := by
      intro x hx y hy hxy hPx
      obtain ⟨⟨hx7, hx1⟩, hxP, _⟩ := hII x hx.1 hx.2
      obtain ⟨⟨hy7, hy1⟩, hyP, _⟩ := hII y hy.1 hy.2
      rw [hxP, P607988be.q_eq] at hPx
      rw [hyP, P607988be.q_eq]
      rcases lt_or_ge β (2 / 5) with hb | hb
      · have hm := P607988be.qt_mono β (k1 - 7 / 12) (y - 7 / 12) (x - 7 / 12) hβ0 hb (by linarith)
          (by linarith) (by linarith)
        have := mul_le_mul_of_nonneg_left hm hβ0
        linarith
      · exfalso
        have hn := P607988be.qt_neg β (k1 - 7 / 12) (x - 7 / 12) hb hβ1 (by linarith) (by linarith)
        have := mul_neg_of_pos_of_neg (show (0:ℝ) < β by linarith) hn
        linarith
    have hf : Continuous (fun k : ℝ => 72 * P607988be.NN β k1 k * P607988be.DD 0 k1 k - P607988be.DD β k1 k * (72 * P607988be.NN 0 k1 k)) := by
      unfold P607988be.DD P607988be.NN; fun_prop
    obtain ⟨t, ht⟩ := P607988be.up_thr R (fun k => equilibriumProfit k1 k 0 ≤ equilibriumProfit k1 k β)
      _ (49 / 144) k1 hf hRb hP hup
    exact ⟨t, fun k2 hS h1 => ht k2 ⟨hS, h1⟩⟩
  · -- β ≥ 2/5
    intro hb k2 hS hk0
    obtain ⟨⟨h7, h1⟩, _, hQ⟩ := hII k2 hS hk0
    rw [hQ, P607988be.q_eq]
    have hn := P607988be.qt_neg β (k1 - 7 / 12) (k2 - 7 / 12) hb hβ1 (by linarith) (by linarith)
    have := mul_neg_of_pos_of_neg (show (0:ℝ) < β by linarith) hn
    linarith
