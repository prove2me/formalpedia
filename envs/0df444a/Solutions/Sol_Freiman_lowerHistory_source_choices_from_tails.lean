-- Prove2me | solution 1 for Freiman.lowerHistory_source_choices_from_tails
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-18T10:36:32.468225+00:00
-- url     : https://prove2.me/submissions/9785f874-2054-41a4-b1a6-abf739302a3c

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

namespace HistDev

/-! ### Certificate-field algebra -/

lemma val_rat (q : ℚ) : certFieldVal (lowerHistoryRat q) = (q : ℝ) := by
  simp [lowerHistoryRat, certFieldVal]

lemma threshold_value (a x y u v : CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold a (x, y) (u, v)) r s =
      certFieldVal a * ((1 + s * certFieldVal u) * (1 + s * certFieldVal v)) /
        ((1 + r * certFieldVal x) * (1 + r * certFieldVal y)) := by
  unfold lowerHistoryThreshold lowerHistorySort
  split_ifs <;>
    simp only [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

lemma complement_holds (b : CertBound) (r s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q := by
  rcases b with ⟨bl, bs, bt⟩
  cases bl <;> cases bs <;>
    simp [lowerHistoryComplement, certBoundHolds, not_le, not_lt]

lemma pb_thr (base : LowerPair) (c : CertField) (i j k l : ℕ) (lo st : Bool)
    (hi : certFieldVal (lowerHistoryTheta i) = lowerTheta i)
    (hj : certFieldVal (lowerHistoryTheta j) = lowerTheta j)
    (hk : certFieldVal (lowerHistoryTheta k) = lowerTheta k)
    (hl : certFieldVal (lowerHistoryTheta l) = lowerTheta l) :
    certThresholdVal (lowerHistoryPB c i j k l lo st).threshold
        (lowerRatio (lowerNormalize base).1) (lowerRatio (lowerNormalize base).2)
      = lowerThreshold base (certFieldVal c) i j k l := by
  show certThresholdVal (lowerHistoryThreshold c (lowerHistoryTheta i, lowerHistoryTheta k)
      (lowerHistoryTheta j, lowerHistoryTheta l)) _ _ = _
  rw [threshold_value, hi, hj, hk, hl]
  rfl

/-! ### Definitional unfoldings of the report's A/H predicates -/

lemma lowerA3_eq (p : LowerPair) :
    lowerA p 3 = (lowerScale (lowerNormalize p) < lowerThreshold p (31/100) 3 63 25 66) := rfl
lemma lowerA9_eq (p : LowerPair) :
    lowerA p 9 = (lowerScale (lowerNormalize p) ≤
      lowerThreshold p ((3 - Real.sqrt 3)/2) 36 63 63 66) := rfl
lemma lowerH2_eq (p : LowerPair) :
    lowerH p 2 = (lowerScale (lowerNormalize p) > lowerThreshold p (37/50) 63 70 66 90) := rfl
lemma lowerH5_eq (p : LowerPair) :
    lowerH p 5 = (lowerScale (lowerNormalize p) < lowerThreshold p (279/500) 35 63 63 70) := rfl
lemma lowerH6_eq (p : LowerPair) :
    lowerH p 6 = (lowerScale (lowerNormalize p) < lowerThreshold p (69/200) 22 65 28 68) := rfl
lemma lowerH7_eq (p : LowerPair) :
    lowerH p 7 = (lowerScale (lowerNormalize p) < lowerThreshold p (161/500) 3 63 25 66) := rfl
lemma lowerH21_eq (p : LowerPair) :
    lowerH p 21 = (lowerScale (lowerNormalize p) <
      lowerThreshold p (|(lowerTheta 63 - lowerTheta 3)/(lowerTheta 20 - lowerTheta 66)|)
        3 20 63 66) := rfl
lemma lowerH23_eq (p : LowerPair) :
    lowerH p 23 = (lowerScale (lowerNormalize p) > lowerThreshold p (139/250) 63 70 66 94) := rfl

/-! ### The H21 constant -/

lemma arith21 (t : ℝ) (ht : t * t = 3) (h1 : (17/10 : ℝ) < t) (h2 : t < 18/10)
    (N D : ℝ) (hN : N = -22/13 + 14/13 * t) (hD : D = -171/429 + 34/429 * t) :
    |N / D| = -2334/781 + 1646/781 * t := by
  subst hN; subst hD
  have hDn : (-171/429 + 34/429 * t) < 0 := by linarith
  have hq : (-22/13 + 14/13 * t) / (-171/429 + 34/429 * t) = 2334/781 - 1646/781 * t := by
    rw [div_eq_iff (ne_of_lt hDn)]
    linear_combination (55964/335049 : ℝ) * ht
  rw [hq, abs_of_nonpos (by linarith)]
  ring

lemma c21_val (h3 : certFieldVal (lowerHistoryTheta 3) = lowerTheta 3)
    (h20 : certFieldVal (lowerHistoryTheta 20) = lowerTheta 20)
    (h63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63)
    (h66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66) :
    certFieldVal (lowerHistoryAbs (lowerHistoryDiv
      (certFieldSub (lowerHistoryTheta 63) (lowerHistoryTheta 3))
      (certFieldSub (lowerHistoryTheta 20) (lowerHistoryTheta 66))))
      = |(lowerTheta 63 - lowerTheta 3) / (lowerTheta 20 - lowerTheta 66)| := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ht : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← pow_two]; exact hsq
  have hnn : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h1 : (17/10 : ℝ) < Real.sqrt 3 := by nlinarith
  have h2 : Real.sqrt 3 < (18/10 : ℝ) := by nlinarith
  have vA : certFieldVal (lowerHistoryTheta 63) - certFieldVal (lowerHistoryTheta 3)
      = -22/13 + 14/13 * Real.sqrt 3 := by
    norm_num [certFieldVal, lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix,
      lowerHistoryDiv, lowerHistoryInv, lowerHistoryRat, lowerHistoryTau,
      certFieldAdd, certFieldScale, certFieldMul, certFieldSub]
    ring
  have vB : certFieldVal (lowerHistoryTheta 20) - certFieldVal (lowerHistoryTheta 66)
      = -171/429 + 34/429 * Real.sqrt 3 := by
    norm_num [certFieldVal, lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix,
      lowerHistoryDiv, lowerHistoryInv, lowerHistoryRat, lowerHistoryTau,
      certFieldAdd, certFieldScale, certFieldMul, certFieldSub]
    ring
  have vC : certFieldVal (lowerHistoryAbs (lowerHistoryDiv
      (certFieldSub (lowerHistoryTheta 63) (lowerHistoryTheta 3))
      (certFieldSub (lowerHistoryTheta 20) (lowerHistoryTheta 66))))
      = -2334/781 + 1646/781 * Real.sqrt 3 := by
    norm_num [certFieldVal, lowerHistoryAbs, lowerHistorySign, lowerHistoryQuadSign,
      lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix,
      lowerHistoryDiv, lowerHistoryInv, lowerHistoryRat, lowerHistoryTau,
      certFieldAdd, certFieldScale, certFieldMul, certFieldSub]
  rw [← h3, ← h20, ← h63, ← h66, vC, vA, vB]
  exact (arith21 (Real.sqrt 3) ht h1 h2 _ _ rfl rfl).symm

/-! ### Bound dictionary -/

section
variable {base : LowerPair}

lemma h2_iff (h63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63)
    (h70 : certFieldVal (lowerHistoryTheta 70) = lowerTheta 70)
    (h66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66)
    (h90 : certFieldVal (lowerHistoryTheta 90) = lowerTheta 90) :
    certBoundHolds lowerHistoryH2 (lowerRatio (lowerNormalize base).1)
      (lowerRatio (lowerNormalize base).2) (lowerScale (lowerNormalize base)) ↔ lowerH base 2 := by
  show certThresholdVal (lowerHistoryPB (lowerHistoryRat (37/50)) 63 70 66 90 true true).threshold
    _ _ < _ ↔ _
  rw [pb_thr base _ 63 70 66 90 true true h63 h70 h66 h90, val_rat, lowerH2_eq]
  norm_num

lemma h5_iff (h35 : certFieldVal (lowerHistoryTheta 35) = lowerTheta 35)
    (h63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63)
    (h70 : certFieldVal (lowerHistoryTheta 70) = lowerTheta 70) :
    certBoundHolds lowerHistoryH5 (lowerRatio (lowerNormalize base).1)
      (lowerRatio (lowerNormalize base).2) (lowerScale (lowerNormalize base)) ↔ lowerH base 5 := by
  show _ < certThresholdVal (lowerHistoryPB (lowerHistoryRat (279/500)) 35 63 63 70 false true).threshold
    _ _ ↔ _
  rw [pb_thr base _ 35 63 63 70 false true h35 h63 h63 h70, val_rat, lowerH5_eq]
  norm_num

lemma h6_iff (h22 : certFieldVal (lowerHistoryTheta 22) = lowerTheta 22)
    (h65 : certFieldVal (lowerHistoryTheta 65) = lowerTheta 65)
    (h28 : certFieldVal (lowerHistoryTheta 28) = lowerTheta 28)
    (h68 : certFieldVal (lowerHistoryTheta 68) = lowerTheta 68) :
    certBoundHolds lowerHistoryH6 (lowerRatio (lowerNormalize base).1)
      (lowerRatio (lowerNormalize base).2) (lowerScale (lowerNormalize base)) ↔ lowerH base 6 := by
  show _ < certThresholdVal (lowerHistoryPB (lowerHistoryRat (69/200)) 22 65 28 68 false true).threshold
    _ _ ↔ _
  rw [pb_thr base _ 22 65 28 68 false true h22 h65 h28 h68, val_rat, lowerH6_eq]
  norm_num

lemma h7_iff (h3 : certFieldVal (lowerHistoryTheta 3) = lowerTheta 3)
    (h63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63)
    (h25 : certFieldVal (lowerHistoryTheta 25) = lowerTheta 25)
    (h66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66) :
    certBoundHolds lowerHistoryH7 (lowerRatio (lowerNormalize base).1)
      (lowerRatio (lowerNormalize base).2) (lowerScale (lowerNormalize base)) ↔ ¬ lowerA base 3 := by
  show certThresholdVal (lowerHistoryPB (lowerHistoryRat (31/100)) 3 63 25 66 true false).threshold
    _ _ ≤ _ ↔ _
  rw [pb_thr base _ 3 63 25 66 true false h3 h63 h25 h66, val_rat, lowerA3_eq]
  norm_num

lemma h7m_iff (h3 : certFieldVal (lowerHistoryTheta 3) = lowerTheta 3)
    (h63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63)
    (h25 : certFieldVal (lowerHistoryTheta 25) = lowerTheta 25)
    (h66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66) :
    certBoundHolds lowerHistoryH7Mixed (lowerRatio (lowerNormalize base).1)
      (lowerRatio (lowerNormalize base).2) (lowerScale (lowerNormalize base)) ↔ lowerH base 7 := by
  show _ < certThresholdVal (lowerHistoryPB (lowerHistoryRat (161/500)) 3 63 25 66 false true).threshold
    _ _ ↔ _
  rw [pb_thr base _ 3 63 25 66 false true h3 h63 h25 h66, val_rat, lowerH7_eq]
  norm_num

lemma h9_iff (h36 : certFieldVal (lowerHistoryTheta 36) = lowerTheta 36)
    (h63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63)
    (h66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66) :
    certBoundHolds lowerHistoryH9 (lowerRatio (lowerNormalize base).1)
      (lowerRatio (lowerNormalize base).2) (lowerScale (lowerNormalize base)) ↔ lowerA base 9 := by
  show _ ≤ certThresholdVal (lowerHistoryPB (⟨3/2, -1/2, 0, 0⟩ : CertField) 36 63 63 66
    false false).threshold _ _ ↔ _
  rw [pb_thr base _ 36 63 63 66 false false h36 h63 h63 h66, lowerA9_eq]
  have : certFieldVal (⟨3/2, -1/2, 0, 0⟩ : CertField) = (3 - Real.sqrt 3)/2 := by
    norm_num [certFieldVal]; ring
  rw [this]

lemma h21_iff (h3 : certFieldVal (lowerHistoryTheta 3) = lowerTheta 3)
    (h20 : certFieldVal (lowerHistoryTheta 20) = lowerTheta 20)
    (h63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63)
    (h66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66) :
    certBoundHolds lowerHistoryH21 (lowerRatio (lowerNormalize base).1)
      (lowerRatio (lowerNormalize base).2) (lowerScale (lowerNormalize base)) ↔ lowerH base 21 := by
  show _ < certThresholdVal (lowerHistoryPB (lowerHistoryAbs (lowerHistoryDiv
      (certFieldSub (lowerHistoryTheta 63) (lowerHistoryTheta 3))
      (certFieldSub (lowerHistoryTheta 20) (lowerHistoryTheta 66)))) 3 20 63 66
      false true).threshold _ _ ↔ _
  rw [pb_thr base _ 3 20 63 66 false true h3 h20 h63 h66, c21_val h3 h20 h63 h66, lowerH21_eq]

lemma h23_iff (h63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63)
    (h70 : certFieldVal (lowerHistoryTheta 70) = lowerTheta 70)
    (h66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66)
    (h94 : certFieldVal (lowerHistoryTheta 94) = lowerTheta 94) :
    certBoundHolds lowerHistoryH23 (lowerRatio (lowerNormalize base).1)
      (lowerRatio (lowerNormalize base).2) (lowerScale (lowerNormalize base)) ↔ lowerH base 23 := by
  show certThresholdVal (lowerHistoryPB (lowerHistoryRat (139/250)) 63 70 66 94 true true).threshold
    _ _ < _ ↔ _
  rw [pb_thr base _ 63 70 66 94 true true h63 h70 h66 h94, val_rat, lowerH23_eq]
  norm_num

end

/-! ### Assembling bound lists -/

lemma atBase_nil (v : LowerPair) : lowerHistoryAtBase v [] := by
  intro b hb; exact absurd hb (List.not_mem_nil)

lemma atBase_cons {v : LowerPair} {b : CertBound} {bs : List CertBound}
    (h1 : certBoundHolds b (lowerRatio v.1) (lowerRatio v.2) (lowerScale v))
    (h2 : lowerHistoryAtBase v bs) : lowerHistoryAtBase v (b :: bs) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h1
  · exact h2 x hx

/-! ### Offered-label exclusions -/

def earlyBad : List LowerLabel := [([2],[]),([3],[]),([],[1]),([2],[1]),([3],[1])]
def lateBad : List LowerLabel := [([2],[]),([3],[]),([],[1]),([3],[1])]

lemma late_ne (p : LowerPair) (l : LowerLabel) (h : l ∈ lowerLateList p) : l ∉ lateBad := by
  classical
  have hc : l ∈ lowerLateCandidates := by
    unfold lowerLateList at h
    split_ifs at h with hex
    · exact ((Classical.choose_spec hex).1 l h).1
    · simp at h
  fin_cases hc <;> decide

lemma early_ne (p : LowerPair) (l : LowerLabel) (h : l ∈ lowerEarlyList p) : l ∉ earlyBad := by
  classical
  unfold lowerEarlyList at h
  split_ifs at h <;> (fin_cases h <;> decide)

lemma eq_2nil (p : LowerPair) (h : (([2],[]) : LowerLabel) ∈ lowerEqualList p) :
    lowerA p 3 ∨ lowerA p 9 := by
  classical
  have hE : (([2],[]) : LowerLabel) ∉ lowerEarlyList p := fun hm => early_ne p _ hm (by decide)
  have hL : (([2],[]) : LowerLabel) ∉ lowerLateList p := fun hm => late_ne p _ hm (by decide)
  unfold lowerEqualList at h
  split_ifs at h <;> simp_all

lemma eq_3nil (p : LowerPair) (h : (([3],[]) : LowerLabel) ∈ lowerEqualList p) : lowerA p 3 := by
  classical
  have hE : (([3],[]) : LowerLabel) ∉ lowerEarlyList p := fun hm => early_ne p _ hm (by decide)
  have hL : (([3],[]) : LowerLabel) ∉ lowerLateList p := fun hm => late_ne p _ hm (by decide)
  unfold lowerEqualList at h
  split_ifs at h <;> simp_all

lemma eq_21 (p : LowerPair) (h : (([2],[1]) : LowerLabel) ∈ lowerEqualList p) :
    ¬ lowerA p 3 ∧ ¬ lowerA p 9 := by
  classical
  have hE : (([2],[1]) : LowerLabel) ∉ lowerEarlyList p := fun hm => early_ne p _ hm (by decide)
  unfold lowerEqualList at h
  split_ifs at h <;> simp_all

lemma eq_31 (p : LowerPair) (h : (([3],[1]) : LowerLabel) ∈ lowerEqualList p) :
    ¬ lowerA p 3 ∧ ¬ lowerA p 9 := by
  classical
  have hE : (([3],[1]) : LowerLabel) ∉ lowerEarlyList p := fun hm => early_ne p _ hm (by decide)
  have hL : (([3],[1]) : LowerLabel) ∉ lowerLateList p := fun hm => late_ne p _ hm (by decide)
  unfold lowerEqualList at h
  split_ifs at h <;> simp_all

lemma eq_n1 (p : LowerPair) (h : (([],[1]) : LowerLabel) ∈ lowerEqualList p) : False := by
  classical
  have hE : (([],[1]) : LowerLabel) ∉ lowerEarlyList p := fun hm => early_ne p _ hm (by decide)
  have hL : (([],[1]) : LowerLabel) ∉ lowerLateList p := fun hm => late_ne p _ hm (by decide)
  unfold lowerEqualList at h
  split_ifs at h <;> simp_all

lemma mx_2nil (p : LowerPair) (h : (([2],[]) : LowerLabel) ∈ lowerMixedList p) :
    ¬ lowerH p 2 ∧ lowerH p 5 := by
  classical
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all

lemma mx_3nil (p : LowerPair) (h : (([3],[]) : LowerLabel) ∈ lowerMixedList p) :
    ¬ lowerH p 2 ∧ lowerH p 5 ∧ lowerH p 6 ∧ lowerH p 7 := by
  classical
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all

lemma mx_n1 (p : LowerPair) (h : (([],[1]) : LowerLabel) ∈ lowerMixedList p) :
    lowerH p 2 ∨ (¬ lowerH p 2 ∧ ¬ lowerH p 5 ∧ ¬ lowerH p 21 ∧
      ¬ lowerEnds (lowerNormalize p).2 [3] ∧ lowerH p 23) := by
  classical
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all

lemma mx_21 (p : LowerPair) (h : (([2],[1]) : LowerLabel) ∈ lowerMixedList p) :
    ¬ lowerH p 2 ∧ ¬ lowerH p 5 := by
  classical
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all

lemma mx_31 (p : LowerPair) (h : (([3],[1]) : LowerLabel) ∈ lowerMixedList p) :
    (¬ lowerH p 2 ∧ lowerH p 5 ∧ (¬ lowerH p 6 ∨ ¬ lowerH p 7)) ∨
    (¬ lowerH p 2 ∧ ¬ lowerH p 5 ∧ ¬ lowerL p) := by
  classical
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all <;> tauto

/-! ### Context bridges -/

lemma parity_iff (base : LowerPair) (C : LowerHistoryContext)
    (hf : lowerHistoryContextFits base C) : (C.parity.1 = C.parity.2) ↔ ¬ lowerMixed base := by
  obtain ⟨-, -, h3⟩ := hf
  unfold lowerMixed
  have m1 := Nat.mod_two_eq_zero_or_one base.1.length
  have m2 := Nat.mod_two_eq_zero_or_one base.2.length
  revert h3
  cases hp1 : C.parity.1 <;> cases hp2 : C.parity.2 <;>
    rcases m1 with m1 | m1 <;> rcases m2 with m2 | m2 <;> simp [m1, m2]

lemma pickOrient3 (base w : LowerPair) (flip : Bool)
    (f1 : lowerEnds base.1 [3] ↔ lowerEnds w.1 [3])
    (f2 : lowerEnds base.2 [3] ↔ lowerEnds w.2 [3]) :
    (([3] : List ℕ+).IsSuffix (lowerHistoryPick w (!flip)))
      ↔ lowerEnds (lowerHistoryOrient base flip).2 [3] := by
  cases flip
  · exact f2.symm
  · exact f1.symm

lemma pickOrient31 (base w : LowerPair) (flip : Bool)
    (f1 : lowerEnds base.1 [3,1] ↔ lowerEnds w.1 [3,1])
    (f2 : lowerEnds base.2 [3,1] ↔ lowerEnds w.2 [3,1]) :
    (([3,1] : List ℕ+).IsSuffix (lowerHistoryPick w flip))
      ↔ lowerEnds (lowerHistoryOrient base flip).1 [3,1] := by
  cases flip
  · exact f1.symm
  · exact f2.symm

end HistDev

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
open HistDev in
theorem solution (ht : ∀ i ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ),
    certFieldVal (lowerHistoryTheta i) = lowerTheta i) :
    LowerHistoryChoiceLaw := by
  classical
  have t3 := ht 3 (by decide)
  have t20 := ht 20 (by decide)
  have t22 := ht 22 (by decide)
  have t25 := ht 25 (by decide)
  have t28 := ht 28 (by decide)
  have t35 := ht 35 (by decide)
  have t36 := ht 36 (by decide)
  have t63 := ht 63 (by decide)
  have t65 := ht 65 (by decide)
  have t66 := ht 66 (by decide)
  have t68 := ht 68 (by decide)
  have t70 := ht 70 (by decide)
  have t90 := ht 90 (by decide)
  have t94 := ht 94 (by decide)
  intro base s l hfit hnorm hlab hoff
  have H2 := h2_iff (base := base) t63 t70 t66 t90
  have H5 := h5_iff (base := base) t35 t63 t70
  have H6 := h6_iff (base := base) t22 t65 t28 t68
  have H7 := h7_iff (base := base) t3 t63 t25 t66
  have H7M := h7m_iff (base := base) t3 t63 t25 t66
  have H9 := h9_iff (base := base) t36 t63 t66
  have H21 := h21_iff (base := base) t3 t20 t63 t66
  have H23 := h23_iff (base := base) t63 t70 t66 t94
  have hpm := parity_iff base s.context hfit
  have hs3 : (([3] : List ℕ+).IsSuffix (lowerHistoryPick s.context.words (!s.wider)))
      ↔ lowerEnds (lowerNormalize base).2 [3] := by
    rw [hnorm]; exact pickOrient3 base s.context.words s.wider hfit.1.2.1 hfit.2.1.2.1
  have hs31 : (([3,1] : List ℕ+).IsSuffix (lowerHistoryPick s.context.words s.wider))
      ↔ lowerL base := by
    show _ ↔ lowerEnds (lowerNormalize base).1 [3,1]
    rw [hnorm]; exact pickOrient31 base s.context.words s.wider hfit.1.2.2 hfit.2.1.2.2
  rw [← hnorm]
  have hmem : l ∈ (if lowerMixed base then lowerMixedList base else lowerEqualList base) := by
    rcases hoff with h | ⟨-, k, hk, hkl⟩
    · exact h
    · exfalso
      subst hkl
      cases k with
      | zero => exact absurd hk (lt_irrefl 0)
      | succ n => revert hlab; simp [lowerHistoryLabels, List.replicate_succ]
  simp only [lowerHistoryLabels, List.mem_cons, List.not_mem_nil, or_false] at hlab
  rcases hlab with rfl | rfl | rfl | rfl | rfl | rfl
  -- l = ([1],[])
  · exact ⟨[], by simp [lowerHistorySourceChoices], atBase_nil _⟩
  -- l = ([2],[])
  · by_cases hpar : s.context.parity.1 = s.context.parity.2
    · have hmix : ¬ lowerMixed base := hpm.mp hpar
      rw [if_neg hmix] at hmem
      have hsc : lowerHistorySourceChoices s ([2],[]) =
          [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7, lowerHistoryH9]] := by
        simp [lowerHistorySourceChoices, hpar]
      by_cases ha3 : lowerA base 3
      · exact ⟨[lowerHistoryComplement lowerHistoryH7], by rw [hsc]; simp,
          atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => (H7.mp hc) ha3)) (atBase_nil _)⟩
      · have ha9 : lowerA base 9 := (eq_2nil base hmem).resolve_left ha3
        exact ⟨[lowerHistoryH7, lowerHistoryH9], by rw [hsc]; simp,
          atBase_cons (H7.mpr ha3) (atBase_cons (H9.mpr ha9) (atBase_nil _))⟩
    · have hmix : lowerMixed base := by by_contra hc; exact hpar (hpm.mpr hc)
      rw [if_pos hmix] at hmem
      obtain ⟨hn2, h5⟩ := mx_2nil base hmem
      exact ⟨[lowerHistoryComplement lowerHistoryH2, lowerHistoryH5],
        by simp [lowerHistorySourceChoices, hpar],
        atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn2 (H2.mp hc)))
          (atBase_cons (H5.mpr h5) (atBase_nil _))⟩
  -- l = ([3],[])
  · by_cases hpar : s.context.parity.1 = s.context.parity.2
    · have hmix : ¬ lowerMixed base := hpm.mp hpar
      rw [if_neg hmix] at hmem
      have ha3 : lowerA base 3 := eq_3nil base hmem
      exact ⟨[lowerHistoryComplement lowerHistoryH7], by simp [lowerHistorySourceChoices, hpar],
        atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => (H7.mp hc) ha3)) (atBase_nil _)⟩
    · have hmix : lowerMixed base := by by_contra hc; exact hpar (hpm.mpr hc)
      rw [if_pos hmix] at hmem
      obtain ⟨hn2, h5, h6, h7⟩ := mx_3nil base hmem
      exact ⟨[lowerHistoryComplement lowerHistoryH2, lowerHistoryH5, lowerHistoryH6,
          lowerHistoryH7Mixed], by simp [lowerHistorySourceChoices, hpar],
        atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn2 (H2.mp hc)))
          (atBase_cons (H5.mpr h5) (atBase_cons (H6.mpr h6)
            (atBase_cons (H7M.mpr h7) (atBase_nil _))))⟩
  -- l = ([],[1])
  · by_cases hpar : s.context.parity.1 = s.context.parity.2
    · have hmix : ¬ lowerMixed base := hpm.mp hpar
      rw [if_neg hmix] at hmem
      exact (eq_n1 base hmem).elim
    · have hmix : lowerMixed base := by by_contra hc; exact hpar (hpm.mpr hc)
      rw [if_pos hmix] at hmem
      by_cases hh2 : lowerH base 2
      · exact ⟨[lowerHistoryH2], by simp [lowerHistorySourceChoices, hpar],
          atBase_cons (H2.mpr hh2) (atBase_nil _)⟩
      · rcases mx_n1 base hmem with h | ⟨-, hn5, hn21, hends, h23⟩
        · exact absurd h hh2
        · have hnsf : ¬ (([3] : List ℕ+).IsSuffix (lowerHistoryPick s.context.words (!s.wider))) :=
            fun hc => hends (hs3.mp hc)
          exact ⟨[lowerHistoryComplement lowerHistoryH2, lowerHistoryComplement lowerHistoryH5,
              lowerHistoryComplement lowerHistoryH21, lowerHistoryH23],
            by simp [lowerHistorySourceChoices, hpar, hnsf],
            atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hh2 (H2.mp hc)))
              (atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn5 (H5.mp hc)))
                (atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn21 (H21.mp hc)))
                  (atBase_cons (H23.mpr h23) (atBase_nil _))))⟩
  -- l = ([2],[1])
  · by_cases hpar : s.context.parity.1 = s.context.parity.2
    · have hmix : ¬ lowerMixed base := hpm.mp hpar
      rw [if_neg hmix] at hmem
      obtain ⟨ha3, ha9⟩ := eq_21 base hmem
      exact ⟨[lowerHistoryH7, lowerHistoryComplement lowerHistoryH9],
        by simp [lowerHistorySourceChoices, hpar],
        atBase_cons (H7.mpr ha3)
          (atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => ha9 (H9.mp hc))) (atBase_nil _))⟩
    · have hmix : lowerMixed base := by by_contra hc; exact hpar (hpm.mpr hc)
      rw [if_pos hmix] at hmem
      obtain ⟨hn2, hn5⟩ := mx_21 base hmem
      exact ⟨[lowerHistoryComplement lowerHistoryH2, lowerHistoryComplement lowerHistoryH5],
        by simp [lowerHistorySourceChoices, hpar],
        atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn2 (H2.mp hc)))
          (atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn5 (H5.mp hc))) (atBase_nil _))⟩
  -- l = ([3],[1])
  · by_cases hpar : s.context.parity.1 = s.context.parity.2
    · have hmix : ¬ lowerMixed base := hpm.mp hpar
      rw [if_neg hmix] at hmem
      obtain ⟨ha3, ha9⟩ := eq_31 base hmem
      exact ⟨[lowerHistoryH7, lowerHistoryComplement lowerHistoryH9],
        by simp [lowerHistorySourceChoices, hpar],
        atBase_cons (H7.mpr ha3)
          (atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => ha9 (H9.mp hc))) (atBase_nil _))⟩
    · have hmix : lowerMixed base := by by_contra hc; exact hpar (hpm.mpr hc)
      rw [if_pos hmix] at hmem
      rcases mx_31 base hmem with ⟨hn2, h5, h67⟩ | ⟨hn2, hn5, hnL⟩
      · by_cases hh6 : lowerH base 6
        · have hn7 : ¬ lowerH base 7 := h67.resolve_left (not_not_intro hh6)
          exact ⟨[lowerHistoryComplement lowerHistoryH2, lowerHistoryH5, lowerHistoryH6,
              lowerHistoryComplement lowerHistoryH7Mixed],
            by simp [lowerHistorySourceChoices, hpar],
            atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn2 (H2.mp hc)))
              (atBase_cons (H5.mpr h5) (atBase_cons (H6.mpr hh6)
                (atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn7 (H7M.mp hc)))
                  (atBase_nil _))))⟩
        · exact ⟨[lowerHistoryComplement lowerHistoryH2, lowerHistoryH5,
              lowerHistoryComplement lowerHistoryH6],
            by simp [lowerHistorySourceChoices, hpar],
            atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn2 (H2.mp hc)))
              (atBase_cons (H5.mpr h5)
                (atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hh6 (H6.mp hc)))
                  (atBase_nil _)))⟩
      · have hnsf : ¬ (([3,1] : List ℕ+).IsSuffix (lowerHistoryPick s.context.words s.wider)) :=
          fun hc => hnL (hs31.mp hc)
        exact ⟨[lowerHistoryComplement lowerHistoryH2, lowerHistoryComplement lowerHistoryH5],
          by simp [lowerHistorySourceChoices, hpar, hnsf],
          atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn2 (H2.mp hc)))
            (atBase_cons ((complement_holds _ _ _ _).mpr (fun hc => hn5 (H5.mp hc)))
              (atBase_nil _))⟩

