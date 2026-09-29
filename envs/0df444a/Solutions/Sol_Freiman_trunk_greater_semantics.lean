-- Prove2me | solution 1 for Freiman.trunk_greater_semantics
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T12:58:57.927582+00:00
-- url     : https://prove2.me/submissions/cfbb7b8e-5bef-4864-8cdd-ef00f3952e82

import Definitions.Def_Freiman_trunkGeometry
import Theorems.Thm_Freiman_lowerHistory_greater_from_sign
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_continuant_determinant
import Theorems.Thm_Freiman_lowerHistory_inv_value
import Theorems.Thm_Freiman_prefixEval_mobius


open Freiman

namespace M7GreaterMobius

private theorem cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem ratio_nonneg (w : List ℕ+) : 0 ≤ lowerRatio w := by
  unfold lowerRatio
  positivity

noncomputable def factors (w : List ℕ+) (x y : ℝ) : ℝ :=
  (1 + lowerRatio w * x) * (1 + lowerRatio w * y)

private theorem factors_pos (w : List ℕ+) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 < factors w x y := by
  have hr := ratio_nonneg w
  unfold factors
  positivity

private theorem pe_diff (w : List ℕ+) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      (-1 : ℝ)^w.length * (x-y) /
        (((lowerCD w).2 : ℝ)^2 * factors w x y) := by
  rw [prefixEval_mobius w x hx, prefixEval_mobius w y hy]
  have hq : (0 : ℝ) < wordContinuantQ w := by
    exact_mod_cast continuant_denominator_pos w
  have hd : (wordContinuantPrevP w : ℝ) * wordContinuantQ w -
      wordContinuantP w * wordContinuantPrevQ w = (-1 : ℝ)^w.length := by
    exact_mod_cast continuant_determinant w
  have hc := cd_eq w
  simp only [factors, lowerRatio, hc]
  field_simp
  nlinarith

private theorem pow_sign (n : ℕ) :
    (-1 : ℝ)^n = if decide (n % 2 = 1) then -1 else 1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

private theorem xor_sign (a b : Bool) :
    (if a.xor b then (-1 : ℝ) else 1) * (if a then -1 else 1) =
      if b then -1 else 1 := by
  cases a <;> cases b <;> norm_num

private theorem common_sign_left (base : LowerPair) (C : LowerHistoryContext) :
    (if lowerHistoryCommonOdd base C then (-1 : ℝ) else 1) *
        (-1 : ℝ)^base.1.length = if C.parity.1 then -1 else 1 := by
  unfold lowerHistoryCommonOdd
  rw [pow_sign]
  exact xor_sign _ _

private theorem common_sign_right (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) :
    (if lowerHistoryCommonOdd base C then (-1 : ℝ) else 1) *
        (-1 : ℝ)^base.2.length = if C.parity.2 then -1 else 1 := by
  have hcommon : lowerHistoryCommonOdd base C =
      (decide (base.2.length % 2 = 1)).xor C.parity.2 := hc.2.2
  rw [hcommon, pow_sign]
  exact xor_sign _ _

private theorem lowerScale_pos (base : LowerPair) : 0 < lowerScale base := by
  unfold lowerScale
  exact div_pos (sq_pos_of_pos (q_pos base.1)) (sq_pos_of_pos (q_pos base.2))

private theorem history_margin_factors_pos
    (base : LowerPair) (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) :
    0 < (1 + lowerRatio base.1 * certFieldVal x.1) *
          (1 + lowerRatio base.1 * certFieldVal y.1) ∧
    0 < (1 + lowerRatio base.2 * certFieldVal x.2) *
          (1 + lowerRatio base.2 * certFieldVal y.2) ∧
    0 < lowerScale base := by
  exact ⟨factors_pos _ _ _ hx.1 hy.1,
    factors_pos _ _ _ hx.2 hy.2, lowerScale_pos base⟩

private theorem history_value_margin
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C)
    (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) :
    let Fx := (1 + lowerRatio base.1 * certFieldVal x.1) *
      (1 + lowerRatio base.1 * certFieldVal y.1)
    let Fy := (1 + lowerRatio base.2 * certFieldVal x.2) *
      (1 + lowerRatio base.2 * certFieldVal y.2)
    let a := (if C.parity.1 then -1 else 1 : ℝ) *
      (certFieldVal x.1-certFieldVal y.1)
    let b := (if C.parity.2 then -1 else 1 : ℝ) *
      (certFieldVal x.2-certFieldVal y.2)
    lowerHistoryValue base C y ≤ lowerHistoryValue base C x ↔
      0 ≤ a*Fy + lowerScale base*b*Fx := by
  dsimp only
  let X1 := certFieldVal x.1
  let X2 := certFieldVal x.2
  let Y1 := certFieldVal y.1
  let Y2 := certFieldVal y.2
  let F1 := factors base.1 X1 Y1
  let F2 := factors base.2 X2 Y2
  let D1 := ((lowerCD base.1).2 : ℝ)
  let D2 := ((lowerCD base.2).2 : ℝ)
  let e := if lowerHistoryCommonOdd base C then (-1 : ℝ) else 1
  let s1 := if C.parity.1 then (-1 : ℝ) else 1
  let s2 := if C.parity.2 then (-1 : ℝ) else 1
  have hF1 : 0 < F1 := factors_pos _ _ _ hx.1 hy.1
  have hF2 : 0 < F2 := factors_pos _ _ _ hx.2 hy.2
  have hD1 : 0 < D1 := q_pos _
  have hD2 : 0 < D2 := q_pos _
  have hs1 : e * (-1 : ℝ)^base.1.length = s1 := common_sign_left base C
  have hs2 : e * (-1 : ℝ)^base.2.length = s2 := common_sign_right base C hc
  have hd1 := pe_diff base.1 X1 Y1 hx.1 hy.1
  have hd2 := pe_diff base.2 X2 Y2 hx.2 hy.2
  have hscale : lowerScale base = D1^2/D2^2 := by rfl
  change e * (4 + prefixEval base.1 Y1 + prefixEval base.2 Y2) ≤
      e * (4 + prefixEval base.1 X1 + prefixEval base.2 X2) ↔
    0 ≤ s1*(X1-Y1)*F2 + lowerScale base*(s2*(X2-Y2))*F1
  rw [show e * (4 + prefixEval base.1 Y1 + prefixEval base.2 Y2) ≤
      e * (4 + prefixEval base.1 X1 + prefixEval base.2 X2) ↔
      0 ≤ e * ((prefixEval base.1 X1-prefixEval base.1 Y1) +
        (prefixEval base.2 X2-prefixEval base.2 Y2)) by
    constructor <;> intro h <;> nlinarith]
  rw [hd1, hd2, hscale]
  have hden : 0 < D1^2*F1*F2 := by positivity
  rw [show e * (((-1 : ℝ)^base.1.length*(X1-Y1))/(D1^2*F1) +
      ((-1 : ℝ)^base.2.length*(X2-Y2))/(D2^2*F2)) =
      (s1*(X1-Y1)*F2 + (D1^2/D2^2)*(s2*(X2-Y2))*F1) /
        (D1^2*F1*F2) by
    field_simp
    calc
      e * ((-1 : ℝ)^base.1.length * (X1-Y1) * D2^2 * F2 +
          D1^2 * F1 * (-1 : ℝ)^base.2.length * (X2-Y2)) =
        (e * (-1 : ℝ)^base.1.length) * (X1-Y1) * D2^2 * F2 +
          D1^2 * F1 * (e * (-1 : ℝ)^base.2.length) * (X2-Y2) := by ring
      _ = _ := by rw [hs1, hs2]; ring]
  constructor
  · intro hq
    rcases div_nonneg_iff.mp hq with h | h
    · exact h.1
    · linarith [h.2, hden]
  · intro h
    exact div_nonneg h hden.le


end M7GreaterMobius

set_option autoImplicit false

namespace GreaterNumeric

private theorem greater_from_sign_numeric (a b L R q : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hq : 0 < q) :
    (if 0 ≤ a ∧ 0 ≤ b then True
     else if a ≤ 0 ∧ b ≤ 0 then False
     else if a < 0 then |a / b| * R / L ≤ q
     else q ≤ |a / b| * R / L) ↔
    0 ≤ a * R + q * b * L := by
  by_cases hpp : 0 ≤ a ∧ 0 ≤ b
  · rw [if_pos hpp]
    constructor
    · intro _
      exact add_nonneg (mul_nonneg hpp.1 hR.le)
        (mul_nonneg (mul_nonneg hq.le hpp.2) hL.le)
    · intro _
      trivial
  · by_cases hnn : a ≤ 0 ∧ b ≤ 0
    · rw [if_neg hpp, if_pos hnn]
      simp only [false_iff, not_le]
      rcases hnn with ⟨ha, hb⟩
      have hstrict : a < 0 ∨ b < 0 := by
        by_contra h
        simp only [not_or, not_lt] at h
        exact hpp ⟨h.1, h.2⟩
      rcases hstrict with ha' | hb'
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_neg_of_pos ha' hR)
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos hq.le hb) hL.le)
      · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg ha hR.le)
          (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hq hb') hL)
    · by_cases ha : a < 0
      · rw [if_neg hpp, if_neg hnn, if_pos ha]
        have hb : 0 < b := by
          by_contra h
          exact hnn ⟨le_of_lt ha, le_of_not_gt h⟩
        rw [abs_div, abs_of_neg ha, abs_of_pos hb]
        rw [show -a / b * R / L = (-a * R) / (b * L) by field_simp]
        rw [div_le_iff₀ (mul_pos hb hL)]
        constructor <;> intro h
        · nlinarith
        · nlinarith
      · rw [if_neg hpp, if_neg hnn, if_neg ha]
        have ha0 : 0 ≤ a := le_of_not_gt ha
        have hb : b < 0 := by
          by_contra h
          exact hpp ⟨ha0, le_of_not_gt h⟩
        rw [abs_div, abs_of_nonneg ha0, abs_of_neg hb]
        rw [show a / -b * R / L = (a * R) / ((-b) * L) by field_simp]
        rw [le_div_iff₀ (mul_pos (neg_pos.mpr hb) hL)]
        constructor <;> intro h
        · nlinarith
        · nlinarith


end GreaterNumeric

open Freiman
namespace Stage13GreaterSigns
set_option maxHeartbeats 2000000

private theorem sort_factors (c : CertField) (x y : CertField × CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * (1+s*certFieldVal y.1) * (1+s*certFieldVal y.2) /
        ((1+r*certFieldVal x.1) * (1+r*certFieldVal x.2)) := by
  unfold certThresholdVal certThresholdNum certThresholdDen lowerHistoryThreshold lowerHistorySort
  split_ifs <;> simp only <;> ring

private theorem field_sub (x y : CertField) :
    certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  simp only [certFieldVal, certFieldSub]
  push_cast
  ring

private theorem field_mul (x y : CertField) :
    certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  have h3 : Real.sqrt (3:ℝ)^2 = 3 := Real.sq_sqrt (by norm_num)
  have h7 : Real.sqrt (7:ℝ)^2 = 7 := Real.sq_sqrt (by norm_num)
  have h37 : Real.sqrt (21:ℝ) = Real.sqrt 3 * Real.sqrt 7 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  simp only [certFieldVal, certFieldMul]
  push_cast
  rw [h37]
  ring_nf
  simp only [h3,h7]
  ring

private theorem field_abs
    (hsg : ∀ z : CertField,
      (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧
      (0 < lowerHistorySign z ↔ 0 < certFieldVal z)) (z : CertField) :
    certFieldVal (lowerHistoryAbs z) = |certFieldVal z| := by
  unfold lowerHistoryAbs
  split_ifs with h
  · have hn : certFieldVal z < 0 := by
      rcases lt_trichotomy (certFieldVal z) 0 with hz | hz | hz
      · exact hz
      · have := (hsg z).1.mpr hz; omega
      · have := (hsg z).2.mpr hz; omega
    rw [abs_of_neg hn]
    simp only [lowerHistoryNeg, certFieldScale, certFieldVal]
    push_cast
    ring
  · rw [abs_of_nonneg]
    by_contra hn
    have hz : certFieldVal z < 0 := lt_of_not_ge hn
    have hsn : 0 ≤ lowerHistorySign z := le_of_not_gt h
    rcases eq_or_lt_of_le hsn with he | hp
    · have := (hsg z).1.mp he.symm; linarith
    · have := (hsg z).2.mp hp; linarith



private theorem sign_relations
    (hsg : ∀ z : CertField,
      (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧
      (0 < lowerHistorySign z ↔ 0 < certFieldVal z)) (z : CertField) (b : Bool) :
    let si : ℤ := (if b then -1 else 1) * lowerHistorySign z
    let a : ℝ := (if b then -1 else 1) * certFieldVal z
    (0 ≤ si ↔ 0 ≤ a) ∧ (si ≤ 0 ↔ a ≤ 0) ∧ (si < 0 ↔ a < 0) := by
  have hle : lowerHistorySign z ≤ 0 ↔ certFieldVal z ≤ 0 := by
    simpa only [not_lt] using not_congr (hsg z).2
  have hlt : lowerHistorySign z < 0 ↔ certFieldVal z < 0 := by
    simp only [lt_iff_le_and_ne, hle, ne_eq, (hsg z).1]
  have hge : 0 ≤ lowerHistorySign z ↔ 0 ≤ certFieldVal z := by
    simpa only [not_lt] using not_congr hlt
  cases b
  · simpa using And.intro hge (And.intro hle hlt)
  · simpa using And.intro hle (And.intro hge (hsg z).2)

private theorem threshold_eval
    (hsg : ∀ z : CertField,
      (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧
      (0 < lowerHistorySign z ↔ 0 < certFieldVal z))
    (x y : CertField × CertField) (r s : ℝ)
    (hdy : certFieldVal x.2 - certFieldVal y.2 ≠ 0) :
    certThresholdVal
      (lowerHistoryThreshold (lowerHistoryAbs (lowerHistoryDiv
        (certFieldSub x.1 y.1) (certFieldSub x.2 y.2))) (x.1,y.1) (x.2,y.2)) r s =
      |(certFieldVal x.1-certFieldVal y.1)/(certFieldVal x.2-certFieldVal y.2)| *
      ((1+s*certFieldVal x.2)*(1+s*certFieldVal y.2)) /
      ((1+r*certFieldVal x.1)*(1+r*certFieldVal y.1)) := by
  rw [sort_factors, field_abs hsg]
  unfold lowerHistoryDiv
  rw [field_mul, lowerHistory_inv_value _ (by simpa only [field_sub] using hdy)]
  simp only [field_sub]
  simp only [div_eq_mul_inv]
  ring

end Stage13GreaterSigns

open Freiman
namespace Stage13GreaterInterpretation
set_option maxHeartbeats 2000000

private theorem interpretation
    (hsg : ∀ z : CertField,
      (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧
      (0 < lowerHistorySign z ↔ 0 < certFieldVal z))
    (C : LowerHistoryContext) (x y : CertField × CertField) (r s q : ℝ)
    (hL : 0 < (1+r*certFieldVal x.1)*(1+r*certFieldVal y.1))
    (hR : 0 < (1+s*certFieldVal x.2)*(1+s*certFieldVal y.2)) (hq : 0 < q) :
    lowerHistoryComparisonHolds (lowerHistoryGreater C x y) r s q ↔
      0 ≤ ((if C.parity.1 then -1 else 1 : ℝ)*(certFieldVal x.1-certFieldVal y.1)) *
          ((1+s*certFieldVal x.2)*(1+s*certFieldVal y.2)) +
        q*((if C.parity.2 then -1 else 1 : ℝ)*(certFieldVal x.2-certFieldVal y.2)) *
          ((1+r*certFieldVal x.1)*(1+r*certFieldVal y.1)) := by
  classical
  let a : ℝ := (if C.parity.1 then -1 else 1)*(certFieldVal x.1-certFieldVal y.1)
  let b : ℝ := (if C.parity.2 then -1 else 1)*(certFieldVal x.2-certFieldVal y.2)
  let si : ℤ := (if C.parity.1 then -1 else 1)*lowerHistorySign (certFieldSub x.1 y.1)
  let sj : ℤ := (if C.parity.2 then -1 else 1)*lowerHistorySign (certFieldSub x.2 y.2)
  let L := (1+r*certFieldVal x.1)*(1+r*certFieldVal y.1)
  let R := (1+s*certFieldVal x.2)*(1+s*certFieldVal y.2)
  have hxsub : certFieldVal (certFieldSub x.1 y.1) = certFieldVal x.1-certFieldVal y.1 := by
    simp only [certFieldVal,certFieldSub]; push_cast; ring
  have hysub : certFieldVal (certFieldSub x.2 y.2) = certFieldVal x.2-certFieldVal y.2 := by
    simp only [certFieldVal,certFieldSub]; push_cast; ring
  have hsa : (0≤si ↔ 0≤a) ∧ (si≤0 ↔ a≤0) ∧ (si<0 ↔ a<0) := by
    simpa only [si,a,hxsub] using Stage13GreaterSigns.sign_relations hsg
      (certFieldSub x.1 y.1) C.parity.1
  have hsb : (0≤sj ↔ 0≤b) ∧ (sj≤0 ↔ b≤0) ∧ (sj<0 ↔ b<0) := by
    simpa only [sj,b,hysub] using Stage13GreaterSigns.sign_relations hsg
      (certFieldSub x.2 y.2) C.parity.2
  change _ ↔ 0 ≤ a*R+q*b*L
  apply Iff.trans ?_ (GreaterNumeric.greater_from_sign_numeric a b L R q hL hR hq)
  have hG : lowerHistoryGreater C x y =
      if 0≤si ∧ 0≤sj then .automatic else if si≤0 ∧ sj≤0 then .impossible else
        .bound ⟨decide (si<0),false,lowerHistoryThreshold
          (lowerHistoryAbs (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2)))
          (x.1,y.1) (x.2,y.2)⟩ := rfl
  rw [hG]
  by_cases hn : 0≤si ∧ 0≤sj
  · have hn' : 0≤a ∧ 0≤b := ⟨hsa.1.mp hn.1,hsb.1.mp hn.2⟩
    simp only [if_pos hn,lowerHistoryComparisonHolds,if_pos hn']
  · have hn' : ¬(0≤a ∧ 0≤b) := fun h => hn ⟨hsa.1.mpr h.1,hsb.1.mpr h.2⟩
    by_cases hp : si≤0 ∧ sj≤0
    · have hp' : a≤0 ∧ b≤0 := ⟨hsa.2.1.mp hp.1,hsb.2.1.mp hp.2⟩
      simp only [if_neg hn,if_pos hp,lowerHistoryComparisonHolds,if_neg hn',if_pos hp']
    · have hp' : ¬(a≤0 ∧ b≤0) := fun h => hp ⟨hsa.2.1.mpr h.1,hsb.2.1.mpr h.2⟩
      have hbne : b≠0 := by
        intro hb
        rcases le_total 0 a with ha | ha
        · exact hn' ⟨ha,by rw [hb]⟩
        · exact hp' ⟨ha,by rw [hb]⟩
      have hdy : certFieldVal x.2-certFieldVal y.2 ≠ 0 := by
        intro h; apply hbne; simp only [b,h,mul_zero]
      have hab : |a/b| = |(certFieldVal x.1-certFieldVal y.1)/
          (certFieldVal x.2-certFieldVal y.2)| := by
        cases h1 : C.parity.1 <;> cases h2 : C.parity.2 <;>
          simp only [a,b,h1,h2,Bool.false_eq_true,if_false,if_true,
            one_mul,neg_one_mul,abs_div,abs_neg]
      have ht := Stage13GreaterSigns.threshold_eval hsg x y r s hdy
      rw [← hab] at ht
      change _ = |a/b| * R/L at ht
      simp only [if_neg hn,if_neg hp,lowerHistoryComparisonHolds,certBoundHolds,
        Bool.false_eq_true,if_false,ht,if_neg hn',if_neg hp']
      by_cases ha : si<0
      · simp only [ha,decide_true,if_true,hsa.2.2.mp ha]
      · have ha' : ¬a<0 := fun h => ha (hsa.2.2.mpr h)
        simp only [ha,decide_false,Bool.false_eq_true,if_false,ha']

end Stage13GreaterInterpretation

open Freiman


open Freiman
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace TrunkGreater15

private theorem rat_square_seven (a b : ℚ)
    (h : (a:ℝ)^2 = 7*(b:ℝ)^2) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    norm_num at h
    exact ⟨h,rfl⟩
  · exfalso
    have hi : Irrational (Real.sqrt (7:ℝ)) := by norm_num
    apply hi
    refine ⟨|a/b|, ?_⟩
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)
    have hr : (((a/b:ℚ):ℝ))^2 = 7 := by
      push_cast
      field_simp
      nlinarith [h]
    have he : Real.sqrt (7:ℝ) = |((a/b:ℚ):ℝ)| := by
      have hn := Real.sqrt_nonneg (7:ℝ)
      have ha := abs_nonneg (((a/b:ℚ):ℝ))
      have habs : |((a/b:ℚ):ℝ)|^2 = 7 := by rw [sq_abs,hr]
      nlinarith
    simpa using he.symm

private theorem rat_square_twenty_one (a b : ℚ)
    (h : (a:ℝ)^2 = 21*(b:ℝ)^2) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    norm_num at h
    exact ⟨h,rfl⟩
  · exfalso
    have hi : Irrational (Real.sqrt (21:ℝ)) := by norm_num
    apply hi
    refine ⟨|a/b|, ?_⟩
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
    have hr : (((a/b:ℚ):ℝ))^2 = 21 := by
      push_cast
      field_simp
      nlinarith [h]
    have he : Real.sqrt (21:ℝ) = |((a/b:ℚ):ℝ)| := by
      have hn := Real.sqrt_nonneg (21:ℝ)
      have ha := abs_nonneg (((a/b:ℚ):ℝ))
      have habs : |((a/b:ℚ):ℝ)|^2 = 21 := by rw [sq_abs,hr]
      nlinarith
    simpa using he.symm

private theorem sqrt3_linear (a b : ℚ)
    (h : (a:ℝ)+(b:ℝ)*Real.sqrt 3 = 0) : a=0 ∧ b=0 := by
  by_cases hb : b=0
  · subst b
    have haR : (a:ℝ)=0 := by simpa using h
    exact ⟨by exact_mod_cast haR,rfl⟩
  · exfalso
    have hi : Irrational (Real.sqrt (3:ℝ)) := by norm_num
    apply hi
    refine ⟨-a/b, ?_⟩
    push_cast
    rw [div_eq_iff (by exact_mod_cast hb)]
    nlinarith

private theorem certFieldVal_injective : Function.Injective certFieldVal := by
  intro x y hxy
  let a := x.a-y.a
  let b := x.b-y.b
  let c := x.c-y.c
  let d := x.d-y.d
  have hz : (a:ℝ)+(b:ℝ)*Real.sqrt 3+(c:ℝ)*Real.sqrt 7+
      (d:ℝ)*Real.sqrt 21 = 0 := by
    dsimp [a,b,c,d]
    simp only [certFieldVal] at hxy
    push_cast at hxy ⊢
    linarith
  have h37 : Real.sqrt (21:ℝ) = Real.sqrt 3 * Real.sqrt 7 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  rw [h37] at hz
  have hs3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hs7 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)
  have hsquare :
      (((a:ℝ)+(b:ℝ)*Real.sqrt 3)^2 -
        7*((c:ℝ)+(d:ℝ)*Real.sqrt 3)^2) = 0 := by
    have hz' : (a:ℝ)+(b:ℝ)*Real.sqrt 3 =
        -Real.sqrt 7*((c:ℝ)+(d:ℝ)*Real.sqrt 3) := by
      nlinarith [hz]
    have hh := congrArg (fun z : ℝ => z^2) hz'
    rw [mul_pow] at hh
    have hneg : (-Real.sqrt (7:ℝ))^2 = 7 := by nlinarith [hs7]
    rw [hneg] at hh
    nlinarith
  have hlin :
      (((a^2+3*b^2-7*c^2-21*d^2:ℚ):ℝ) +
        ((2*a*b-14*c*d:ℚ):ℝ)*Real.sqrt 3) = 0 := by
    push_cast
    nlinarith
  obtain ⟨hU,hV⟩ := sqrt3_linear
    (a^2+3*b^2-7*c^2-21*d^2) (2*a*b-14*c*d) hlin
  have hnorm : (a^2-3*b^2)^2 = (7*(c^2-3*d^2))^2 := by
    have hid : (a^2-3*b^2)^2 - 49*(c^2-3*d^2)^2 =
        (a^2+3*b^2-7*c^2-21*d^2)*(a^2+3*b^2+7*c^2+21*d^2) +
        (2*a*b-14*c*d)*(-6*a*b-42*c*d) := by ring
    rw [hU,hV] at hid
    nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hnorm) with hn | hn
  · have hbd : (b:ℝ)^2 = 7*(d:ℝ)^2 := by
      exact_mod_cast (by nlinarith [hU,hn] : b^2=7*d^2)
    obtain ⟨hb,hd⟩ := rat_square_seven b d hbd
    have hac : (a:ℝ)^2 = 7*(c:ℝ)^2 := by
      exact_mod_cast (by simp [hb,hd] at hU; nlinarith [hU] : a^2=7*c^2)
    obtain ⟨ha,hc⟩ := rat_square_seven a c hac
    simp only [a,b,c,d] at ha hb hc hd
    rcases x with ⟨xa,xb,xc,xd⟩
    rcases y with ⟨ya,yb,yc,yd⟩
    simp only at ha hb hc hd ⊢
    congr <;> linarith
  · have had : (a:ℝ)^2 = 21*(d:ℝ)^2 := by
      exact_mod_cast (by nlinarith [hU,hn] : a^2=21*d^2)
    obtain ⟨ha,hd⟩ := rat_square_twenty_one a d had
    have hbc : (3*b:ℝ)^2 = 21*(c:ℝ)^2 := by
      exact_mod_cast (by simp [ha,hd] at hU; nlinarith [hU] : (3*b)^2=21*c^2)
    obtain ⟨hb,hc⟩ := rat_square_twenty_one (3*b) c (by
      simpa only [Rat.cast_mul, Rat.cast_ofNat] using hbc)
    have hb0 : b=0 := by linarith
    simp only [a,b,c,d] at ha hb0 hc hd
    rcases x with ⟨xa,xb,xc,xd⟩
    rcases y with ⟨ya,yb,yc,yd⟩
    simp only at ha hb0 hc hd ⊢
    congr <;> linarith

end TrunkGreater15

namespace TrunkGreater15

private theorem greater_strict_numeric (a b L R q : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hq : 0 < q)
    (hne : ¬(a=0 ∧ b=0)) :
    (if 0 ≤ a ∧ 0 ≤ b then True
     else if a ≤ 0 ∧ b ≤ 0 then False
     else if a < 0 then |a / b| * R / L < q
     else q < |a / b| * R / L) ↔
    0 < a * R + q * b * L := by
  by_cases hpp : 0 ≤ a ∧ 0 ≤ b
  · rw [if_pos hpp]
    have hs : 0 < a ∨ 0 < b := by
      rcases hpp with ⟨ha,hb⟩
      rcases ha.eq_or_lt with ha | ha
      · exact Or.inr (lt_of_le_of_ne hb (fun h => hne ⟨ha.symm,h.symm⟩))
      · exact Or.inl ha
    constructor
    · intro _
      rcases hs with ha | hb
      · exact add_pos_of_pos_of_nonneg (mul_pos ha hR)
          (mul_nonneg (mul_nonneg hq.le hpp.2) hL.le)
      · exact add_pos_of_nonneg_of_pos (mul_nonneg hpp.1 hR.le)
          (mul_pos (mul_pos hq hb) hL)
    · intro _; trivial
  · by_cases hnn : a ≤ 0 ∧ b ≤ 0
    · rw [if_neg hpp, if_pos hnn]
      simp only [false_iff, not_lt]
      rcases hnn with ⟨ha,hb⟩
      have hs : a < 0 ∨ b < 0 := by
        by_contra h
        simp only [not_or,not_lt] at h
        exact hpp ⟨h.1,h.2⟩
      rcases hs with ha' | hb'
      · exact (add_neg_of_neg_of_nonpos (mul_neg_of_neg_of_pos ha' hR)
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos hq.le hb) hL.le)).le
      · exact (add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg ha hR.le)
          (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hq hb') hL)).le
    · by_cases ha : a < 0
      · rw [if_neg hpp, if_neg hnn, if_pos ha]
        have hb : 0 < b := by
          by_contra h
          exact hnn ⟨le_of_lt ha, le_of_not_gt h⟩
        rw [abs_div, abs_of_neg ha, abs_of_pos hb]
        rw [show -a / b * R / L = (-a * R) / (b * L) by field_simp]
        rw [div_lt_iff₀ (mul_pos hb hL)]
        constructor <;> intro h <;> nlinarith
      · rw [if_neg hpp, if_neg hnn, if_neg ha]
        have ha0 : 0 ≤ a := le_of_not_gt ha
        have hb : b < 0 := by
          by_contra h
          exact hpp ⟨ha0, le_of_not_gt h⟩
        rw [abs_div, abs_of_nonneg ha0, abs_of_neg hb]
        rw [show a / -b * R / L = (a * R) / ((-b) * L) by field_simp]
        rw [lt_div_iff₀ (mul_pos (neg_pos.mpr hb) hL)]
        constructor <;> intro h <;> nlinarith

end TrunkGreater15

namespace TrunkGreater15

private theorem history_value_margin_strict
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C)
    (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) :
    let Fx := (1 + lowerRatio base.1 * certFieldVal x.1) *
      (1 + lowerRatio base.1 * certFieldVal y.1)
    let Fy := (1 + lowerRatio base.2 * certFieldVal x.2) *
      (1 + lowerRatio base.2 * certFieldVal y.2)
    let a := (if C.parity.1 then -1 else 1 : ℝ) *
      (certFieldVal x.1-certFieldVal y.1)
    let b := (if C.parity.2 then -1 else 1 : ℝ) *
      (certFieldVal x.2-certFieldVal y.2)
    lowerHistoryValue base C y < lowerHistoryValue base C x ↔
      0 < a*Fy + lowerScale base*b*Fx := by
  dsimp only
  let X1 := certFieldVal x.1
  let X2 := certFieldVal x.2
  let Y1 := certFieldVal y.1
  let Y2 := certFieldVal y.2
  let F1 := M7GreaterMobius.factors base.1 X1 Y1
  let F2 := M7GreaterMobius.factors base.2 X2 Y2
  let D1 := ((lowerCD base.1).2 : ℝ)
  let D2 := ((lowerCD base.2).2 : ℝ)
  let e := if lowerHistoryCommonOdd base C then (-1 : ℝ) else 1
  let s1 := if C.parity.1 then (-1 : ℝ) else 1
  let s2 := if C.parity.2 then (-1 : ℝ) else 1
  have hF1 : 0 < F1 := M7GreaterMobius.factors_pos _ _ _ hx.1 hy.1
  have hF2 : 0 < F2 := M7GreaterMobius.factors_pos _ _ _ hx.2 hy.2
  have hD1 : 0 < D1 := M7GreaterMobius.q_pos _
  have hD2 : 0 < D2 := M7GreaterMobius.q_pos _
  have hs1 : e * (-1 : ℝ)^base.1.length = s1 :=
    M7GreaterMobius.common_sign_left base C
  have hs2 : e * (-1 : ℝ)^base.2.length = s2 :=
    M7GreaterMobius.common_sign_right base C hc
  have hd1 := M7GreaterMobius.pe_diff base.1 X1 Y1 hx.1 hy.1
  have hd2 := M7GreaterMobius.pe_diff base.2 X2 Y2 hx.2 hy.2
  have hscale : lowerScale base = D1^2/D2^2 := by rfl
  change e * (4 + prefixEval base.1 Y1 + prefixEval base.2 Y2) <
      e * (4 + prefixEval base.1 X1 + prefixEval base.2 X2) ↔
    0 < s1*(X1-Y1)*F2 + lowerScale base*(s2*(X2-Y2))*F1
  rw [show e * (4 + prefixEval base.1 Y1 + prefixEval base.2 Y2) <
      e * (4 + prefixEval base.1 X1 + prefixEval base.2 X2) ↔
      0 < e * ((prefixEval base.1 X1-prefixEval base.1 Y1) +
        (prefixEval base.2 X2-prefixEval base.2 Y2)) by
    constructor <;> intro h <;> nlinarith]
  rw [hd1,hd2,hscale]
  have hden : 0 < D1^2*F1*F2 := by positivity
  rw [show e * (((-1 : ℝ)^base.1.length*(X1-Y1))/(D1^2*F1) +
      ((-1 : ℝ)^base.2.length*(X2-Y2))/(D2^2*F2)) =
      (s1*(X1-Y1)*F2 + (D1^2/D2^2)*(s2*(X2-Y2))*F1) /
        (D1^2*F1*F2) by
    field_simp
    calc
      e * ((-1 : ℝ)^base.1.length * (X1-Y1) * D2^2 * F2 +
          D1^2 * F1 * (-1 : ℝ)^base.2.length * (X2-Y2)) =
        (e * (-1 : ℝ)^base.1.length) * (X1-Y1) * D2^2 * F2 +
          D1^2 * F1 * (e * (-1 : ℝ)^base.2.length) * (X2-Y2) := by ring
      _ = _ := by rw [hs1,hs2]; ring]
  constructor
  · intro hq
    rcases div_pos_iff.mp hq with h | h
    · exact h.1
    · exact (not_lt_of_ge hden.le h.2).elim
  · intro h
    exact div_pos h hden

end TrunkGreater15

namespace TrunkGreater15

private theorem strict_interpretation
    (C : LowerHistoryContext) (x y : CertField × CertField) (r s q : ℝ)
    (hL : 0 < (1+r*certFieldVal x.1)*(1+r*certFieldVal y.1))
    (hR : 0 < (1+s*certFieldVal x.2)*(1+s*certFieldVal y.2)) (hq : 0 < q) :
    lowerHistoryComparisonHolds (trunkGreater C x y true) r s q ↔
      0 < ((if C.parity.1 then -1 else 1 : ℝ)*(certFieldVal x.1-certFieldVal y.1)) *
          ((1+s*certFieldVal x.2)*(1+s*certFieldVal y.2)) +
        q*((if C.parity.2 then -1 else 1 : ℝ)*(certFieldVal x.2-certFieldVal y.2)) *
          ((1+r*certFieldVal x.1)*(1+r*certFieldVal y.1)) := by
  classical
  by_cases heq : x=y
  · subst y
    simp [trunkGreater,lowerHistoryGreater,certFieldSub,lowerHistorySign,
      lowerHistoryQuadSign,lowerHistoryRatSign]
    change ¬ False
    simp
  let a : ℝ := (if C.parity.1 then -1 else 1)*(certFieldVal x.1-certFieldVal y.1)
  let b : ℝ := (if C.parity.2 then -1 else 1)*(certFieldVal x.2-certFieldVal y.2)
  let si : ℤ := (if C.parity.1 then -1 else 1)*lowerHistorySign (certFieldSub x.1 y.1)
  let sj : ℤ := (if C.parity.2 then -1 else 1)*lowerHistorySign (certFieldSub x.2 y.2)
  let L := (1+r*certFieldVal x.1)*(1+r*certFieldVal y.1)
  let R := (1+s*certFieldVal x.2)*(1+s*certFieldVal y.2)
  have hxsub : certFieldVal (certFieldSub x.1 y.1) = certFieldVal x.1-certFieldVal y.1 := by
    simp only [certFieldVal,certFieldSub]; push_cast; ring
  have hysub : certFieldVal (certFieldSub x.2 y.2) = certFieldVal x.2-certFieldVal y.2 := by
    simp only [certFieldVal,certFieldSub]; push_cast; ring
  have hsa : (0≤si ↔ 0≤a) ∧ (si≤0 ↔ a≤0) ∧ (si<0 ↔ a<0) := by
    simpa only [si,a,hxsub] using Stage13GreaterSigns.sign_relations
      lowerHistory_sign_value (certFieldSub x.1 y.1) C.parity.1
  have hsb : (0≤sj ↔ 0≤b) ∧ (sj≤0 ↔ b≤0) ∧ (sj<0 ↔ b<0) := by
    simpa only [sj,b,hysub] using Stage13GreaterSigns.sign_relations
      lowerHistory_sign_value (certFieldSub x.2 y.2) C.parity.2
  have habne : ¬(a=0 ∧ b=0) := by
    rintro ⟨ha,hb⟩
    have hx1 : certFieldVal x.1 = certFieldVal y.1 := by
      dsimp [a] at ha
      split at ha <;> linarith
    have hx2 : certFieldVal x.2 = certFieldVal y.2 := by
      dsimp [b] at hb
      split at hb <;> linarith
    apply heq
    exact Prod.ext (certFieldVal_injective hx1) (certFieldVal_injective hx2)
  change _ ↔ 0 < a*R+q*b*L
  apply Iff.trans ?_ (greater_strict_numeric a b L R q hL hR hq habne)
  have hG : trunkGreater C x y true =
      if 0≤si ∧ 0≤sj then .automatic else if si≤0 ∧ sj≤0 then .impossible else
        .bound ⟨decide (si<0),true,lowerHistoryThreshold
          (lowerHistoryAbs (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2)))
          (x.1,y.1) (x.2,y.2)⟩ := by
    unfold trunkGreater lowerHistoryGreater
    dsimp only [si,sj]
    split_ifs <;> simp_all
  rw [hG]
  by_cases hn : 0≤si ∧ 0≤sj
  · have hn' : 0≤a ∧ 0≤b := ⟨hsa.1.mp hn.1,hsb.1.mp hn.2⟩
    simp only [if_pos hn,lowerHistoryComparisonHolds,if_pos hn']
  · have hn' : ¬(0≤a ∧ 0≤b) := fun h => hn ⟨hsa.1.mpr h.1,hsb.1.mpr h.2⟩
    by_cases hp : si≤0 ∧ sj≤0
    · have hp' : a≤0 ∧ b≤0 := ⟨hsa.2.1.mp hp.1,hsb.2.1.mp hp.2⟩
      simp only [if_neg hn,if_pos hp,lowerHistoryComparisonHolds,if_neg hn',if_pos hp']
    · have hp' : ¬(a≤0 ∧ b≤0) := fun h => hp ⟨hsa.2.1.mpr h.1,hsb.2.1.mpr h.2⟩
      have hbne : b≠0 := by
        intro hb
        rcases le_total 0 a with ha | ha
        · exact hn' ⟨ha,by rw [hb]⟩
        · exact hp' ⟨ha,by rw [hb]⟩
      have hdy : certFieldVal x.2-certFieldVal y.2 ≠ 0 := by
        intro h; apply hbne; simp only [b,h,mul_zero]
      have hab : |a/b| = |(certFieldVal x.1-certFieldVal y.1)/
          (certFieldVal x.2-certFieldVal y.2)| := by
        cases h1 : C.parity.1 <;> cases h2 : C.parity.2 <;>
          simp only [a,b,h1,h2,Bool.false_eq_true,if_false,if_true,
            one_mul,neg_one_mul,abs_div,abs_neg]
      have ht := Stage13GreaterSigns.threshold_eval lowerHistory_sign_value x y r s hdy
      rw [← hab] at ht
      change _ = |a/b| * R/L at ht
      simp only [if_neg hn,if_neg hp,lowerHistoryComparisonHolds,certBoundHolds,
        Bool.true_eq_false,if_true,ht,if_neg hn',if_neg hp']
      by_cases ha : si<0
      · simp only [ha,decide_true,if_true,hsa.2.2.mp ha]
      · have ha' : ¬a<0 := fun h => ha (hsa.2.2.mpr h)
        simp only [ha,decide_false,Bool.false_eq_true,if_false,ha']

end TrunkGreater15

open Freiman

private theorem trunk_greater_core : TrunkGreaterLaw := by
  intro base C hc x y hx hy strict
  cases strict
  · have heq : trunkGreater C x y false = lowerHistoryGreater C x y := by
      let dx := certFieldSub x.1 y.1
      let dy := certFieldSub x.2 y.2
      let sx := (if C.parity.1 then -1 else 1) * lowerHistorySign dx
      let sy := (if C.parity.2 then -1 else 1) * lowerHistorySign dy
      let b : CertBound := ⟨decide (sx < 0), false,
        lowerHistoryThreshold (lowerHistoryAbs (lowerHistoryDiv dx dy))
          (x.1,y.1) (x.2,y.2)⟩
      have hG : lowerHistoryGreater C x y =
          if 0 ≤ sx ∧ 0 ≤ sy then .automatic else
          if sx ≤ 0 ∧ sy ≤ 0 then .impossible else .bound b := by
        rfl
      unfold trunkGreater
      rw [hG]
      by_cases hp : 0 ≤ sx ∧ 0 ≤ sy
      · simp [hp, b]
      · by_cases hn : sx ≤ 0 ∧ sy ≤ 0
        · simp [hp, hn]
        · simp [hp, hn, b]
    rw [heq]
    exact lowerHistory_greater_from_sign lowerHistory_sign_value base C hc x y hx hy
  · obtain ⟨hFx,hFy,hq⟩ :=
      M7GreaterMobius.history_margin_factors_pos base x y hx hy
    exact (TrunkGreater15.strict_interpretation C x y
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) hFx hFy hq).trans
        (TrunkGreater15.history_value_margin_strict base C hc x y hx hy).symm


theorem solution :
    TrunkGreaterLaw := by
  exact trunk_greater_core

#print axioms solution
