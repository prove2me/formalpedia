-- Prove2me | solution 1 for Freiman.lowerHistory_reached_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T13:11:22.340661+00:00
-- url     : https://prove2.me/submissions/d769562b-25b8-4db6-b0a7-965e4e05818d

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_continuant_determinant
import Theorems.Thm_Freiman_lowerHistory_inv_value
import Theorems.Thm_Freiman_prefixEval_mobius


open Freiman
namespace M7Goodness14

private theorem prefix_nonneg (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ prefixEval w z := by
  induction w with
  | nil => exact hz
  | cons a w ih =>
    simp only [prefixEval]
    positivity

private theorem tau_nonneg : 0 ≤ certFieldVal lowerHistoryTau := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  norm_num [certFieldVal, lowerHistoryTau]

private theorem endval_nonneg (C : LowerHistoryContext) (w : LowerPair)
    (upper side short : Bool) :
    0 ≤ certFieldVal (lowerHistoryEndVal C w upper side short) := by
  unfold lowerHistoryEndVal
  rw [lowerHistory_cf_value _ _ tau_nonneg]
  exact prefix_nonneg _ _ tau_nonneg

private theorem equal_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEqualCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  by_cases hn : (lowerHistoryNatural C w upper false ||
      lowerHistoryNatural C w upper true) = true
  · simp only [lowerHistoryEqualCases, hn, ↓reduceIte,
      List.mem_singleton, Prod.mk.injEq] at hz
    rcases hz with ⟨rfl, rfl⟩
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩
  · dsimp only [lowerHistoryEqualCases] at hz
    rw [if_neg hn] at hz
    simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, shortened, _, heq⟩ := hz
    cases heq
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩

private theorem endpoint_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEndpointCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  unfold lowerHistoryEndpointCases at hz
  split_ifs at hz with hp
  · exact equal_nonneg C w upper z cs hz
  · simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, ⟨v,bs⟩, hv, heq⟩ := hz
    cases heq
    split_ifs at hv
    · exact equal_nonneg _ _ _ _ _ hv
    · simp only [List.mem_singleton, Prod.mk.injEq] at hv
      rcases hv with ⟨rfl, rfl⟩
      exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩

private theorem field_sub (x y : CertField) :
    certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  simp only [certFieldVal, certFieldSub]
  push_cast
  ring

private theorem sign_nonneg (z : CertField) (b : Bool) :
    (0 ≤ (if b then -1 else 1 : ℤ) * lowerHistorySign z) ↔
      (0 ≤ (if b then -1 else 1 : ℝ) * certFieldVal z) := by
  have hsg := lowerHistory_sign_value z
  have hle : lowerHistorySign z ≤ 0 ↔ certFieldVal z ≤ 0 := by
    simpa only [not_lt] using not_congr hsg.2
  have hlt : lowerHistorySign z < 0 ↔ certFieldVal z < 0 := by
    simp only [lt_iff_le_and_ne, hle, ne_eq, hsg.1]
  have hge : 0 ≤ lowerHistorySign z ↔ 0 ≤ certFieldVal z := by
    simpa only [not_lt] using not_congr hlt
  cases b
  · simpa using hge
  · simpa using hle

private theorem value_mono (hg : LowerHistoryGreaterLaw) (base : LowerPair)
    (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2)
    (h1 : 0 ≤ (if C.parity.1 then -1 else 1 : ℝ) *
      (certFieldVal x.1 - certFieldVal y.1))
    (h2 : 0 ≤ (if C.parity.2 then -1 else 1 : ℝ) *
      (certFieldVal x.2 - certFieldVal y.2)) :
    lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
  have hs1 : 0 ≤ (if C.parity.1 then -1 else 1 : ℤ) *
      lowerHistorySign (certFieldSub x.1 y.1) :=
    (sign_nonneg _ _).mpr (by simpa only [field_sub] using h1)
  have hs2 : 0 ≤ (if C.parity.2 then -1 else 1 : ℤ) *
      lowerHistorySign (certFieldSub x.2 y.2) :=
    (sign_nonneg _ _).mpr (by simpa only [field_sub] using h2)
  apply (hg base C hc x y hx hy).mp
  simp only [lowerHistoryGreater, hs1, hs2, and_self, ↓reduceIte,
    lowerHistoryComparisonHolds]

end M7Goodness14


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
namespace GoodFields15

private def Valid (b : CertBound) : Prop :=
  0 < certFieldVal b.threshold.c ∧
  0 ≤ certFieldVal b.threshold.x0 ∧ 0 ≤ certFieldVal b.threshold.x1 ∧
  0 ≤ certFieldVal b.threshold.y0 ∧ 0 ≤ certFieldVal b.threshold.y1

private theorem extreme_nonneg (maximum : Bool) (zs : List CertField)
    (hz : ∀ z ∈ zs, 0 ≤ certFieldVal z) :
    0 ≤ certFieldVal (lowerHistoryExtreme maximum zs) := by
  have hf (xs : List CertField) (a : CertField) (ha : 0 ≤ certFieldVal a)
      (hxs : ∀ z ∈ xs, 0 ≤ certFieldVal z) :
      0 ≤ certFieldVal (xs.foldl (fun a b =>
        if decide (0 < lowerHistorySign (certFieldSub b a)) = maximum then b else a) a) := by
    induction xs generalizing a with
    | nil => exact ha
    | cons b xs ih =>
      simp only [List.foldl_cons]
      split_ifs
      · exact ih b (hxs b (by simp)) (fun z hz => hxs z (by simp [hz]))
      · exact ih a ha (fun z hz => hxs z (by simp [hz]))
  cases zs with
  | nil => norm_num [lowerHistoryExtreme,lowerHistoryRat,certFieldVal]
  | cons a xs =>
    exact hf (a::xs) a (hz a (by simp)) hz

private def hull (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) : CertField × CertField :=
  let es := lowerHistoryEndpointCases C w upper
  (lowerHistoryExtreme (upper.xor C.parity.1) (es.map (fun z => z.1.1)),
   lowerHistoryExtreme (upper.xor C.parity.2) (es.map (fun z => z.1.2)))

private theorem hull_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) :
    0 ≤ certFieldVal (hull C w upper).1 ∧ 0 ≤ certFieldVal (hull C w upper).2 := by
  constructor
  · apply extreme_nonneg
    intro a ha
    obtain ⟨⟨z,cs⟩,hz,rfl⟩ := List.mem_map.mp ha
    exact (M7Goodness14.endpoint_nonneg C w upper z cs hz).1
  · apply extreme_nonneg
    intro a ha
    obtain ⟨⟨z,cs⟩,hz,rfl⟩ := List.mem_map.mp ha
    exact (M7Goodness14.endpoint_nonneg C w upper z cs hz).2

private theorem bound_fields (C : LowerHistoryContext) (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2)
    (b : CertBound) (hg : lowerHistoryGreater C x y = .bound b) : Valid b := by
  let dx := certFieldSub x.1 y.1
  let dy := certFieldSub x.2 y.2
  let sx := (if C.parity.1 then -1 else 1 : ℤ) * lowerHistorySign dx
  let sy := (if C.parity.2 then -1 else 1 : ℤ) * lowerHistorySign dy
  change (if 0 ≤ sx ∧ 0 ≤ sy then LowerHistoryComparison.automatic else
    if sx ≤ 0 ∧ sy ≤ 0 then LowerHistoryComparison.impossible else LowerHistoryComparison.bound
      ⟨decide (sx < 0),false,lowerHistoryThreshold
        (lowerHistoryAbs (lowerHistoryDiv dx dy)) (x.1,y.1) (x.2,y.2)⟩) = LowerHistoryComparison.bound b at hg
  split_ifs at hg with hp hn <;> try contradiction
  have hsx : sx ≠ 0 := by intro h; omega
  have hsy : sy ≠ 0 := by intro h; omega
  have hdx : certFieldVal dx ≠ 0 := by
    intro h
    apply hsx
    simp [sx,(lowerHistory_sign_value dx).1.mpr h]
  have hdy : certFieldVal dy ≠ 0 := by
    intro h
    apply hsy
    simp [sy,(lowerHistory_sign_value dy).1.mpr h]
  have hc : 0 < certFieldVal (lowerHistoryAbs (lowerHistoryDiv dx dy)) := by
    rw [Stage13GreaterSigns.field_abs lowerHistory_sign_value]
    unfold lowerHistoryDiv
    rw [Stage13GreaterSigns.field_mul,lowerHistory_inv_value dy hdy]
    exact abs_pos.mpr (mul_ne_zero hdx (inv_ne_zero hdy))
  injection hg with hb
  subst b
  unfold Valid lowerHistoryThreshold lowerHistorySort
  split <;> split <;> simp_all

private def envelopeComparison (C : LowerHistoryContext) (u v : LowerPair) : LowerHistoryComparison :=
  lowerHistoryGreater C (hull C u true) (hull C v false)

private def comparisonBounds : LowerHistoryComparison → Option (List CertBound)
  | .automatic => some []
  | .impossible => none
  | .bound b => some [b]

private theorem relaxed_unroll (C : LowerHistoryContext) :
    lowerHistoryRelaxedGoodness C =
      (comparisonBounds (envelopeComparison C ([1],[]) ([2],[]))).bind (fun bs =>
        (comparisonBounds (envelopeComparison C ([2],[]) ([1],[]))).map (fun cs => bs ++ cs)) := by
  unfold lowerHistoryRelaxedGoodness envelopeComparison hull comparisonBounds
  simp only [Bool.true_xor, Bool.false_xor]
  split <;> split <;> simp_all [List.forIn_cons, List.forIn_nil]

private theorem envelope_fields (C : LowerHistoryContext) (u v : LowerPair)
    (bs : List CertBound) (he : comparisonBounds (envelopeComparison C u v) = some bs) :
    ∀ b ∈ bs, Valid b := by
  cases hg : envelopeComparison C u v with
  | automatic =>
    have heq : bs = [] := by simpa [hg,comparisonBounds] using he
    simp [heq]
  | impossible => simp [hg,comparisonBounds] at he
  | bound b =>
    have hb : [b] = bs := by simpa [hg,comparisonBounds] using he
    subst bs
    intro a ha
    have heq : a = b := by simpa using ha
    subst a
    exact bound_fields C _ _ (hull_nonneg C u true) (hull_nonneg C v false) b hg

private theorem relaxed_fields (C : LowerHistoryContext) (bs : List CertBound)
    (h : lowerHistoryRelaxedGoodness C = some bs) : ∀ b ∈ bs, Valid b := by
  rw [relaxed_unroll] at h
  obtain ⟨xs,hxs,hmap⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ys,hys,hbs⟩ := Option.map_eq_some_iff.mp hmap
  subst bs
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact envelope_fields C _ _ xs hxs b hb
  · exact envelope_fields C _ _ ys hys b hb

end GoodFields15


open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ReachedGood15

private theorem rawStep_append (base words : LowerPair) (wide : Bool) (l : LowerLabel) :
    lowerHistoryRawStep (lowerHistoryAppend base words) wide l =
      lowerHistoryAppend base (lowerHistoryRawStep words wide l) := by
  cases wide <;> simp [lowerHistoryRawStep, lowerHistoryAppend, List.append_assoc]

private theorem fold_append (base : LowerPair) :
    ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool),
      List.foldl (fun s step => (lowerHistoryRawStep s.1 s.2 step.1,
        if step.2 then !s.2 else s.2))
          (lowerHistoryAppend base r.1, r.2) xs =
      let z := List.foldl (fun s step => (lowerHistoryRawStep s.1 s.2 step.1,
        if step.2 then !s.2 else s.2)) r xs
      (lowerHistoryAppend base z.1, z.2) := by
  intro xs
  induction xs with
  | nil => intro r; rfl
  | cons step tail ih =>
      intro r
      simp only [List.foldl_cons]
      rw [rawStep_append]
      simpa using ih (lowerHistoryRawStep r.1 r.2 step.1,
        if step.2 then !r.2 else r.2)

private theorem replay_append (base : LowerPair) (p : LowerHistoryPath) (j : ℕ) :
    (lowerHistoryReplay base p j).1 =
      lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1 ∧
    (lowerHistoryReplay base p j).2 = (lowerHistoryReplay ([],[]) p j).2 := by
  unfold lowerHistoryReplay
  have hi : lowerHistoryRawStep base false p.entry =
      lowerHistoryAppend base (lowerHistoryRawStep ([],[]) false p.entry) := by
    simpa [lowerHistoryAppend] using rawStep_append base ([],[]) false p.entry
  rw [hi]
  have hf := fold_append base (p.steps.take j)
    (lowerHistoryRawStep ([],[]) false p.entry, p.initialWider)
  exact ⟨by simpa using congrArg Prod.fst hf, by simpa using congrArg Prod.snd hf⟩

private theorem decide_add_odd (m n : ℕ) :
    decide ((m+n) % 2 = 1) =
      (decide (m % 2 = 1)).xor (decide (n % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [Nat.add_mod, hm, hn]

private theorem even_of_decide_not_odd (n : ℕ) (h : decide (n % 2 = 1) = false) :
    n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · exact hn
  · simp [hn] at h

private theorem advance_shape (r : LowerPair × Bool) (s : LowerHistoryState)
    (l : LowerLabel) (reflect : Bool)
    (hshape : s.context.parity =
        (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
      s.wider = r.2) :
    let r' := (lowerHistoryRawStep r.1 r.2 l, if reflect then !r.2 else r.2)
    let s' := lowerHistoryAdvance s l reflect
    s'.context.parity =
        (decide (r'.1.1.length % 2 = 1), decide (r'.1.2.length % 2 = 1)) ∧
      s'.wider = r'.2 := by
  rcases r with ⟨words,wide⟩
  rcases s with ⟨C,swide,marked,previous⟩
  simp only at hshape ⊢
  unfold lowerHistoryAdvance
  dsimp only
  rw [hshape.1, hshape.2]
  cases wide <;> cases reflect <;>
    simp [lowerHistoryAdvance, lowerHistoryRawStep, List.length_append,
      decide_add_odd, Bool.xor_comm]

private theorem fold_shape :
    ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool) (s : LowerHistoryState),
      (s.context.parity =
          (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
        s.wider = r.2) →
      let rr := List.foldl (fun z step => (lowerHistoryRawStep z.1 z.2 step.1,
        if step.2 then !z.2 else z.2)) r xs
      let ss := xs.foldl (fun z step => lowerHistoryAdvance z step.1 step.2) s
      ss.context.parity =
          (decide (rr.1.1.length % 2 = 1), decide (rr.1.2.length % 2 = 1)) ∧
        ss.wider = rr.2 := by
  intro xs
  induction xs with
  | nil => intro r s hs; exact hs
  | cons step tail ih =>
      intro r s hs
      simp only [List.foldl_cons]
      rcases step with ⟨l,reflect⟩
      apply ih
      exact advance_shape r s l reflect hs

private theorem state_replay_shape (p : LowerHistoryPath) (j : ℕ) :
    let r := lowerHistoryReplay ([],[]) p j
    let s := lowerHistoryStateAt p j
    s.context.parity =
      (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
    s.wider = r.2 := by
  classical
  unfold lowerHistoryReplay lowerHistoryStateAt
  apply fold_shape
  simp [lowerHistoryInitialState, lowerHistoryRawStep]


private theorem suffixContext_snoc (u v : List ℕ+) (a : ℕ+)
    (h : lowerHistorySuffixContext u v) :
    lowerHistorySuffixContext (u++[a]) (v++[a]) := by
  rcases h with ⟨⟨pre,hpre⟩,h3,h31⟩
  refine ⟨⟨pre,by simpa [List.append_assoc] using congrArg (fun z => z ++ [a]) hpre⟩,?_,?_⟩
  · simp [lowerEnds, ← List.reverse_prefix]
  · have h3r : [3] <+: u.reverse ↔ [3] <+: v.reverse := by
      simpa [lowerEnds, ← List.reverse_prefix] using h3
    simp [lowerEnds, ← List.reverse_prefix, h3r]

private theorem suffixContext_append (u v w : List ℕ+)
    (h : lowerHistorySuffixContext u v) :
    lowerHistorySuffixContext (u++w) (v++w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w a ih =>
      simpa [List.append_assoc] using suffixContext_snoc (u++w) (v++w) a ih

private theorem state_words (p : LowerHistoryPath) (j : ℕ) :
    let source : LowerPair :=
      (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
    (lowerHistoryStateAt p j).context.words =
      lowerHistoryAppend source (lowerHistoryWordsAt p j) := by
  let source : LowerPair :=
    (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
  have aux : ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool)
      (s : LowerHistoryState),
      s.context.words = lowerHistoryAppend source r.1 ∧ s.wider = r.2 →
      let rr := xs.foldl (fun z step =>
        (lowerHistoryRawStep z.1 z.2 step.1, if step.2 then !z.2 else z.2)) r
      let ss := xs.foldl (fun z step => lowerHistoryAdvance z step.1 step.2) s
      ss.context.words = lowerHistoryAppend source rr.1 ∧ ss.wider = rr.2 := by
    intro xs
    induction xs with
    | nil => intro r s hs; exact hs
    | cons step tail ih =>
        intro r s hs
        simp only [List.foldl_cons]
        apply ih
        constructor
        · simp only [lowerHistoryAdvance]
          rw [hs.1, hs.2, rawStep_append]
        · simp only [lowerHistoryAdvance]
          rw [hs.2]
          cases r.2 <;> cases step.2 <;> rfl
  unfold lowerHistoryStateAt lowerHistoryWordsAt lowerHistoryReplay
  have ha := aux (p.steps.take j)
    (lowerHistoryRawStep ([],[]) false p.entry,p.initialWider)
    (lowerHistoryInitialState p) (by
      constructor
      · simp only [lowerHistoryInitialState]
        dsimp [source]
        simpa [lowerHistoryAppend] using rawStep_append source ([],[]) false p.entry
      · rfl)
  exact ha.1

private theorem reached_state_context (base : LowerPair) (p : LowerHistoryPath) (j : ℕ)
    (hbase1 : lowerHistorySuffixContext base.1 p.context)
    (hbase2 : lowerHistorySuffixContext base.2
      (if p.catalog = .initial then [3,1,3] else [3,1]))
    (hpar : base.1.length % 2 = base.2.length % 2) :
    let words := lowerHistoryWordsAt p j
    let s := lowerHistoryStateAt p j
    lowerHistoryContextFits
      (lowerHistoryOrient (lowerHistoryAppend base words) s.wider)
      ⟨lowerHistoryOrient s.context.words s.wider,
        if s.wider then (s.context.parity.2,s.context.parity.1) else s.context.parity⟩ := by
  let words := lowerHistoryWordsAt p j
  let s := lowerHistoryStateAt p j
  let source : LowerPair :=
    (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
  have hsw := state_words p j
  have hshape := state_replay_shape p j
  have hpard : decide (base.1.length % 2 = 1) =
      decide (base.2.length % 2 = 1) := by rw [hpar]
  have hctx1 := suffixContext_append base.1 source.1 words.1 hbase1
  have hctx2 := suffixContext_append base.2 source.2 words.2 hbase2
  change lowerHistoryContextFits
    (lowerHistoryOrient (lowerHistoryAppend base words) s.wider)
    ⟨lowerHistoryOrient s.context.words s.wider,
      if s.wider then (s.context.parity.2,s.context.parity.1) else s.context.parity⟩
  have hsw' : s.context.words = lowerHistoryAppend source words := by
    simpa [s, source, words] using hsw
  have hshape' : s.context.parity =
      (decide (words.1.length % 2 = 1), decide (words.2.length % 2 = 1)) := by
    simpa [s, words, lowerHistoryWordsAt] using hshape.1
  cases hw : s.wider <;>
    simp only [lowerHistoryOrient, hw, Bool.false_eq_true, Bool.true_eq_false,
      if_false, if_true, Prod.fst, Prod.snd, ↓reduceIte]
  · refine ⟨?_,?_,?_⟩
    · simpa [hsw', source, lowerHistoryAppend] using hctx1
    · simpa [hsw', source, lowerHistoryAppend] using hctx2
    · rw [hshape']
      simp only [lowerHistoryAppend, List.length_append, decide_add_odd]
      rw [hpard]
      cases decide (base.2.length % 2 = 1) <;>
        cases decide (words.1.length % 2 = 1) <;>
        cases decide (words.2.length % 2 = 1) <;> decide
  · refine ⟨?_,?_,?_⟩
    · simpa [hsw', source, lowerHistoryAppend] using hctx2
    · simpa [hsw', source, lowerHistoryAppend] using hctx1
    · rw [hshape']
      simp only [lowerHistoryAppend, List.length_append, decide_add_odd]
      rw [hpard]
      cases decide (base.2.length % 2 = 1) <;>
        cases decide (words.1.length % 2 = 1) <;>
        cases decide (words.2.length % 2 = 1) <;> decide

private theorem normalize_wide (p : LowerPair) :
    lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
  unfold lowerNormalize
  split_ifs with h
  · exact h
  · exact (lt_of_not_ge h).le

private theorem normalize_idem (p : LowerPair) :
    lowerNormalize (lowerNormalize p) = lowerNormalize p := by
  conv_lhs => rw [lowerNormalize]
  exact if_pos (normalize_wide p)

private theorem normalize_good (p : LowerPair) (h : lowerGood p) :
    lowerGood (lowerNormalize p) := by
  simpa only [lowerGood, lowerChild, normalize_idem] using h

end ReachedGood15

open Freiman

private theorem reached_goodness_core (hg : LowerHistoryGoodnessLaw)
    (hpull : LowerHistoryPullLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) (base : LowerPair) (p : LowerHistoryPath)
    (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryGoodEvents base p := by
  rcases hr with ⟨start,flip,hlen,hreal,hsource⟩
  have hbase2 : lowerHistorySuffixContext base.2
      (if p.catalog = .initial then [3,1,3] else [3,1]) := by
    by_cases hi : p.catalog = .initial
    · have hend : lowerEnds base.2 [3,1,3] := by simpa [hi] using hreal.2.1
      have hnot31 : ¬ lowerEnds base.2 [3,1] := by
        intro h31
        have ha := hend.getLast (by simp)
        have hb := h31.getLast (by simp)
        have : (3 : ℕ+) = 1 := ha.trans hb.symm
        norm_num at this
      have hconst3 : lowerEnds ([3,1,3] : List ℕ+) [3] :=
        ⟨[3,1],rfl⟩
      have hconstnot31 : ¬ lowerEnds ([3,1,3] : List ℕ+) [3,1] := by
        intro hc
        have ha := hc.getLast (by simp)
        norm_num at ha
      simp only [hi, if_true]
      refine ⟨hend,?_,?_⟩
      · constructor
        · intro _; exact hconst3
        · intro _; exact hconst3.trans hend
      · constructor
        · exact fun hb => (hnot31 hb).elim
        · exact fun hb => (hconstnot31 hb).elim
    · have hr2 := hreal.2.1
      rw [if_neg hi] at hr2
      have hend : lowerEnds base.2 [3,1] := hr2.1
      have hnot3 : ¬ lowerEnds base.2 [3] := by
        intro h3
        have ha := hend.getLast (by simp)
        have hb := h3.getLast (by simp)
        have : (1 : ℕ+) = 3 := ha.trans hb.symm
        norm_num at this
      have hconstnot3 : ¬ lowerEnds ([3,1] : List ℕ+) [3] := by
        intro hc
        have ha := hc.getLast (by simp)
        norm_num at ha
      have hconst31 : lowerEnds ([3,1] : List ℕ+) [3,1] := ⟨[],rfl⟩
      simp only [hi, if_false]
      refine ⟨hend,?_,?_⟩
      · constructor
        · exact fun hb => (hnot3 hb).elim
        · exact fun hb => (hconstnot3 hb).elim
      · constructor
        · intro _; exact hconst31
        · intro _; exact hend
  intro j hj
  let words := lowerHistoryWordsAt p j
  let s := lowerHistoryStateAt p j
  let q := lowerHistoryOrient (lowerHistoryAppend base words) s.wider
  let C : LowerHistoryContext :=
    ⟨lowerHistoryOrient s.context.words s.wider,
      if s.wider then (s.context.parity.2,s.context.parity.1) else s.context.parity⟩
  have hfit : lowerHistoryContextFits q C := by
    exact ReachedGood15.reached_state_context base p j hreal.1 hbase2 hreal.2.2.1
  have hrj := hreal.2.2.2 j hj
  have hq : q = lowerNormalize (h (start+j)) := by
    have happ := ReachedGood15.replay_append base p j
    have hshape := ReachedGood15.state_replay_shape p j
    calc
      q = lowerHistoryOrient (lowerHistoryReplay base p j).1
          (lowerHistoryReplay base p j).2 := by
        dsimp only [q]
        rw [hshape.2, ← happ.2]
        congr 1
        exact happ.1.symm
      _ = lowerNormalize (h (start+j)) := hrj.2.2.symm
  have hs := hh.2.1 (start+j) (by omega)
  have hqnorm : lowerNormalize q = q := by
    rw [hq]
    exact ReachedGood15.normalize_idem (h (start+j))
  have hqgood : lowerGood q := by
    rw [hq]
    exact ReachedGood15.normalize_good (h (start+j)) hs.2.1
  obtain ⟨bs,hbs,hholds⟩ := hg q C hfit hqnorm hqgood
  refine ⟨bs.map (fun b => lowerHistoryPull b words s.wider),?_,?_⟩
  · simp [lowerHistoryNecessary, C, words, s, hbs]
  · intro d hd
    obtain ⟨b,hbm,rfl⟩ := List.mem_map.mp hd
    have hv := GoodFields15.relaxed_fields C bs hbs b hbm
    have hbq : lowerHistoryAtBase q [b] := by
      intro a ha
      have hab : a = b := by simpa using ha
      subst a
      exact hholds b hbm
    have hpulled := (hpull base words b s.wider hv.1 hv.2.1 hv.2.2.1
      hv.2.2.2.1 hv.2.2.2.2).mp (by simpa [q] using hbq)
    exact hpulled _ (by simp)


theorem solution (hg : LowerHistoryGoodnessLaw) (hpull : LowerHistoryPullLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryGoodEvents base p := by
  exact reached_goodness_core hg hpull t h n hh base p hp hr

#print axioms solution
