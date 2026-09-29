-- Prove2me | solution 3 for Freiman.lowerHistory_source_choices
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T13:39:55.677148+00:00
-- url     : https://prove2.me/submissions/01ab994e-e0f9-4fa2-9818-d56c11c5b5cf

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_theta_values
import Theorems.Thm_Freiman_lowerHistory_inv_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Mathlib.Tactic

open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Choices15

private theorem threshold_value (c : CertField) (x y : CertField × CertField)
    (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * ((1+s*certFieldVal y.1)*(1+s*certFieldVal y.2)) /
        ((1+r*certFieldVal x.1)*(1+r*certFieldVal x.2)) := by
  simp only [lowerHistoryThreshold, lowerHistorySort]
  split <;> split <;>
    simp only [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

private theorem field_sub (x y : CertField) :
    certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  simp only [certFieldVal, certFieldSub]
  push_cast
  ring

private theorem field_mul (x y : CertField) :
    certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  have h21 : Real.sqrt 21 = Real.sqrt 3 * Real.sqrt 7 := by
    rw [show (21:ℝ) = 3*7 by norm_num, Real.sqrt_mul (by norm_num)]
  have h3' : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have h7' : (Real.sqrt 7)^2 = 7 := Real.sq_sqrt (by norm_num)
  simp only [certFieldVal, certFieldMul, h21]
  push_cast
  ring_nf
  rw [h3', h7']
  ring

private theorem field_abs (z : CertField) :
    certFieldVal (lowerHistoryAbs z) = |certFieldVal z| := by
  unfold lowerHistoryAbs
  split_ifs with h
  · have hn : certFieldVal z < 0 := by
      rcases lt_trichotomy (certFieldVal z) 0 with hz | hz | hz
      · exact hz
      · have := (lowerHistory_sign_value z).1.mpr hz; omega
      · have := (lowerHistory_sign_value z).2.mpr hz; omega
    rw [abs_of_neg hn]
    simp only [lowerHistoryNeg, certFieldScale, certFieldVal]
    push_cast
    ring
  · rw [abs_of_nonneg]
    by_contra hn
    have hz : certFieldVal z < 0 := lt_of_not_ge hn
    have hsn : 0 ≤ lowerHistorySign z := le_of_not_gt h
    rcases eq_or_lt_of_le hsn with he | hp
    · have := (lowerHistory_sign_value z).1.mp he.symm; linarith
    · have := (lowerHistory_sign_value z).2.mp hp; linarith

private theorem field_div (x y : CertField) (hy : certFieldVal y ≠ 0) :
    certFieldVal (lowerHistoryDiv x y) = certFieldVal x / certFieldVal y := by
  simp only [lowerHistoryDiv, field_mul, lowerHistory_inv_value y hy, div_eq_mul_inv]

private theorem h21_den_ne :
    certFieldVal (certFieldSub (lowerHistoryTheta 20) (lowerHistoryTheta 66)) ≠ 0 := by
  have h20 : lowerHistoryTheta 20 = (⟨42/143,1/429,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryTau,
      lowerHistoryDiv,lowerHistoryInv,lowerHistoryRat,certFieldMul,certFieldAdd,
      certFieldScale]
  have h66 : lowerHistoryTheta 66 = (⟨9/13,-1/13,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryTau,
      lowerHistoryDiv,lowerHistoryInv,lowerHistoryRat,certFieldMul,certFieldAdd,
      certFieldScale]
  rw [h20,h66]
  norm_num [certFieldSub]
  simp only [certFieldVal]
  push_cast
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  intro h
  nlinarith

private theorem threshold_values (p : LowerPair) :
    certThresholdVal lowerHistoryH7.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p (31/100) 3 63 25 66 ∧
    certThresholdVal lowerHistoryH9.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 ∧
    certThresholdVal lowerHistoryH2.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p (37/50) 63 70 66 90 ∧
    certThresholdVal lowerHistoryH5.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p (279/500) 35 63 63 70 ∧
    certThresholdVal lowerHistoryH6.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p (69/200) 22 65 28 68 ∧
    certThresholdVal lowerHistoryH7Mixed.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p (161/500) 3 63 25 66 ∧
    certThresholdVal lowerHistoryH21.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p
        (|(lowerTheta 63-lowerTheta 3)/(lowerTheta 20-lowerTheta 66)|) 3 20 63 66 ∧
    certThresholdVal lowerHistoryH23.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p (139/250) 63 70 66 94 := by
  simp only [lowerHistoryH7,lowerHistoryH9,lowerHistoryH2,lowerHistoryH5,
    lowerHistoryH6,lowerHistoryH7Mixed,lowerHistoryH21,lowerHistoryH23,
    lowerHistoryPB,threshold_value,lowerThreshold,
    lowerHistory_theta_values 3 (by simp),lowerHistory_theta_values 20 (by simp),
    lowerHistory_theta_values 22 (by simp),lowerHistory_theta_values 25 (by simp),
    lowerHistory_theta_values 28 (by simp),lowerHistory_theta_values 35 (by simp),
    lowerHistory_theta_values 36 (by simp),lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 65 (by simp),lowerHistory_theta_values 66 (by simp),
    lowerHistory_theta_values 68 (by simp),lowerHistory_theta_values 70 (by simp),
    lowerHistory_theta_values 90 (by simp),lowerHistory_theta_values 94 (by simp),
    field_abs,field_div _ _ h21_den_ne,field_sub]
  norm_num [lowerHistoryRat,certFieldVal]
  ring

end Choices15

namespace Choices15

private theorem source_choice_member (s : LowerHistoryState) (l : LowerLabel)
    (bs : List CertBound) (hbs : bs ∈ lowerHistorySourceChoices s l)
    (b : CertBound) (hb : b ∈ bs) :
    b ∈ [lowerHistoryH7, lowerHistoryComplement lowerHistoryH7,
      lowerHistoryH9, lowerHistoryComplement lowerHistoryH9,
      lowerHistoryH2, lowerHistoryComplement lowerHistoryH2,
      lowerHistoryH5, lowerHistoryComplement lowerHistoryH5,
      lowerHistoryH6, lowerHistoryComplement lowerHistoryH6,
      lowerHistoryH7Mixed, lowerHistoryComplement lowerHistoryH7Mixed,
      lowerHistoryH21, lowerHistoryComplement lowerHistoryH21,
      lowerHistoryH23, lowerHistoryComplement lowerHistoryH23] := by
  unfold lowerHistorySourceChoices at hbs
  split_ifs at hbs <;> simp_all <;> aesop

end Choices15

namespace Choices15

private def pull_ok (b : CertBound) : Prop :=
    0 < certFieldVal b.threshold.c ∧
    0 ≤ certFieldVal b.threshold.x0 ∧ 0 ≤ certFieldVal b.threshold.x1 ∧
    0 ≤ certFieldVal b.threshold.y0 ∧ 0 ≤ certFieldVal b.threshold.y1

private theorem threshold_ok (lo strict : Bool) (c : CertField)
    (x y : CertField × CertField) (hc : 0 < certFieldVal c)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) :
    pull_ok ⟨lo,strict,lowerHistoryThreshold c x y⟩ := by
  simp only [pull_ok,lowerHistoryThreshold,lowerHistorySort]
  split <;> split <;> simp_all

private theorem tail_nonnegative :
    0 ≤ lowerAlpha ∧ 0 ≤ lowerBeta ∧ 0 ≤ lowerTau := by
  have h21 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have n21 := Real.sqrt_nonneg (21:ℝ)
  have n3 := Real.sqrt_nonneg (3:ℝ)
  dsimp [lowerAlpha,lowerBeta,lowerTau]
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem pe_nonnegative (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih => simp only [prefixEval]; positivity

private theorem theta_nonnegative (i : ℕ)
    (hi : i ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ)) :
    0 ≤ certFieldVal (lowerHistoryTheta i) := by
  rw [lowerHistory_theta_values i hi]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [lowerTheta]
  all_goals apply pe_nonnegative
  all_goals rcases tail_nonnegative with ⟨ha,hb,ht⟩
  all_goals positivity

private theorem h21_num_ne :
    certFieldVal (certFieldSub (lowerHistoryTheta 63) (lowerHistoryTheta 3)) ≠ 0 := by
  have h63 : lowerHistoryTheta 63 = (⟨4/13,1/13,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryTau,
      lowerHistoryDiv,lowerHistoryInv,lowerHistoryRat,certFieldMul,certFieldAdd,
      certFieldScale]
  have h3 : lowerHistoryTheta 3 = (⟨2,-1,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryTau,
      lowerHistoryDiv,lowerHistoryInv,lowerHistoryRat,certFieldMul,certFieldAdd,
      certFieldScale]
  rw [h63,h3]
  norm_num [certFieldSub]
  simp only [certFieldVal]
  push_cast
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  intro h
  nlinarith

private theorem h21_c_pos : 0 < certFieldVal lowerHistoryH21.threshold.c := by
  change 0 < certFieldVal (lowerHistoryAbs (lowerHistoryDiv
    (certFieldSub (lowerHistoryTheta 63) (lowerHistoryTheta 3))
    (certFieldSub (lowerHistoryTheta 20) (lowerHistoryTheta 66))))
  rw [field_abs]
  apply abs_pos.mpr
  rw [field_div _ _ h21_den_ne]
  exact div_ne_zero h21_num_ne h21_den_ne

private theorem pb_ok (c : CertField) (i j k m : ℕ) (lo strict : Bool)
    (hc : 0 < certFieldVal c)
    (hi : i ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ))
    (hj : j ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ))
    (hk : k ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ))
    (hm : m ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ)) :
    pull_ok (lowerHistoryPB c i j k m lo strict) := by
  apply threshold_ok
  · exact hc
  · exact ⟨theta_nonnegative i hi,theta_nonnegative k hk⟩
  · exact ⟨theta_nonnegative j hj,theta_nonnegative m hm⟩

private theorem source_basic_fields :
    (∀ b ∈ [lowerHistoryH7,lowerHistoryH9,lowerHistoryH2,lowerHistoryH5,
      lowerHistoryH6,lowerHistoryH7Mixed,lowerHistoryH21,lowerHistoryH23], pull_ok b) := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply pb_ok <;> norm_num [lowerHistoryRat,certFieldVal]
  · apply pb_ok
    · norm_num [certFieldVal]
      have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
      have hn := Real.sqrt_nonneg (3:ℝ)
      nlinarith
    all_goals simp
  · apply pb_ok <;> norm_num [lowerHistoryRat,certFieldVal]
  · apply pb_ok <;> norm_num [lowerHistoryRat,certFieldVal]
  · apply pb_ok <;> norm_num [lowerHistoryRat,certFieldVal]
  · apply pb_ok <;> norm_num [lowerHistoryRat,certFieldVal]
  · apply pb_ok
    · exact h21_c_pos
    all_goals simp
  · apply pb_ok <;> norm_num [lowerHistoryRat,certFieldVal]

/-- Every source-choice certificate has the positivity needed by `LowerHistoryPullLaw`. -/
private theorem source_choice_fields (s : LowerHistoryState) (l : LowerLabel)
    (bs : List CertBound) (hbs : bs ∈ lowerHistorySourceChoices s l)
    (b : CertBound) (hb : b ∈ bs) :
    0 < certFieldVal b.threshold.c ∧
    0 ≤ certFieldVal b.threshold.x0 ∧ 0 ≤ certFieldVal b.threshold.x1 ∧
    0 ≤ certFieldVal b.threshold.y0 ∧ 0 ≤ certFieldVal b.threshold.y1 := by
  have hm := source_choice_member s l bs hbs b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact source_basic_fields lowerHistoryH7 (by simp)
  · simpa [lowerHistoryComplement,pull_ok] using source_basic_fields lowerHistoryH7 (by simp)
  · exact source_basic_fields lowerHistoryH9 (by simp)
  · simpa [lowerHistoryComplement,pull_ok] using source_basic_fields lowerHistoryH9 (by simp)
  · exact source_basic_fields lowerHistoryH2 (by simp)
  · simpa [lowerHistoryComplement,pull_ok] using source_basic_fields lowerHistoryH2 (by simp)
  · exact source_basic_fields lowerHistoryH5 (by simp)
  · simpa [lowerHistoryComplement,pull_ok] using source_basic_fields lowerHistoryH5 (by simp)
  · exact source_basic_fields lowerHistoryH6 (by simp)
  · simpa [lowerHistoryComplement,pull_ok] using source_basic_fields lowerHistoryH6 (by simp)
  · exact source_basic_fields lowerHistoryH7Mixed (by simp)
  · simpa [lowerHistoryComplement,pull_ok] using source_basic_fields lowerHistoryH7Mixed (by simp)
  · exact source_basic_fields lowerHistoryH21 (by simp)
  · simpa [lowerHistoryComplement,pull_ok] using source_basic_fields lowerHistoryH21 (by simp)
  · exact source_basic_fields lowerHistoryH23 (by simp)
  · simpa [lowerHistoryComplement,pull_ok] using source_basic_fields lowerHistoryH23 (by simp)


private theorem mixed_iff_context_parity_ne (base : LowerPair)
    (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C) :
    lowerMixed base ↔ C.parity.1 ≠ C.parity.2 := by
  have hm₁ : base.1.length % 2 < 2 := Nat.mod_lt _ (by omega)
  have hm₂ : base.2.length % 2 < 2 := Nat.mod_lt _ (by omega)
  have he₁ : base.1.length % 2 = 0 ∨ base.1.length % 2 = 1 := by omega
  have he₂ : base.2.length % 2 = 0 ∨ base.2.length % 2 = 1 := by omega
  rcases C with ⟨words,⟨p₁,p₂⟩⟩
  unfold lowerHistoryContextFits at hc
  unfold lowerMixed
  simp only at hc ⊢
  rcases he₁ with h₁ | h₁ <;> rcases he₂ with h₂ | h₂ <;>
    cases p₁ <;> cases p₂ <;> simp_all [Bool.xor]


private theorem norm_second_three_iff (base : LowerPair) (C : LowerHistoryContext)
    (wider : Bool) (hc : lowerHistoryContextFits base C)
    (hn : lowerNormalize base = lowerHistoryOrient base wider) :
    lowerEnds (lowerNormalize base).2 [3] ↔
      ([3] : List ℕ+).IsSuffix (lowerHistoryPick C.words (!wider)) := by
  rcases hc with ⟨hc₁,hc₂,_⟩
  cases wider
  · simp only [lowerHistoryOrient,lowerHistoryPick,Bool.not_false,if_true] at hn ⊢
    rw [hn]
    exact hc₂.2.1
  · simp only [lowerHistoryOrient,lowerHistoryPick,Bool.not_true,if_false] at hn ⊢
    rw [hn]
    exact hc₁.2.1

private theorem norm_first_31_iff (base : LowerPair) (C : LowerHistoryContext)
    (wider : Bool) (hc : lowerHistoryContextFits base C)
    (hn : lowerNormalize base = lowerHistoryOrient base wider) :
    lowerL base ↔ ([3,1] : List ℕ+).IsSuffix (lowerHistoryPick C.words wider) := by
  rcases hc with ⟨hc₁,hc₂,_⟩
  unfold lowerL
  cases wider
  · simp only [lowerHistoryOrient,lowerHistoryPick,if_false] at hn ⊢
    rw [hn]
    exact hc₁.2.2
  · simp only [lowerHistoryOrient,lowerHistoryPick,if_true] at hn ⊢
    rw [hn]
    exact hc₂.2.2

private theorem a3_cut (p : LowerPair) (h : lowerA p 3) :
    lowerHistoryAtBase (lowerNormalize p) [lowerHistoryComplement lowerHistoryH7] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  subst b
  change lowerScale (lowerNormalize p) < certThresholdVal lowerHistoryH7.threshold _ _
  rw [(threshold_values p).1]
  exact h

private theorem not_a3_a9_cut (p : LowerPair) (h3 : ¬lowerA p 3)
    (h9 : lowerA p 9) :
    lowerHistoryAtBase (lowerNormalize p) [lowerHistoryH7,lowerHistoryH9] := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl
  · change certThresholdVal lowerHistoryH7.threshold _ _ ≤ lowerScale (lowerNormalize p)
    rw [(threshold_values p).1]
    exact le_of_not_gt h3
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH9.threshold _ _
    rw [(threshold_values p).2.1]
    exact h9

private theorem not_a3_not_a9_cut (p : LowerPair) (h3 : ¬lowerA p 3)
    (h9 : ¬lowerA p 9) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl
  · change certThresholdVal lowerHistoryH7.threshold _ _ ≤ lowerScale (lowerNormalize p)
    rw [(threshold_values p).1]
    exact le_of_not_gt h3
  · change certThresholdVal lowerHistoryH9.threshold _ _ < lowerScale (lowerNormalize p)
    rw [(threshold_values p).2.1]
    exact lt_of_not_ge h9

private theorem mixed_2_cut (p : LowerPair) (h2 : ¬lowerH p 2) (h5 : lowerH p 5) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryComplement lowerHistoryH2,lowerHistoryH5] := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH2.threshold _ _
    rw [(threshold_values p).2.2.1]
    exact le_of_not_gt h2
  · change lowerScale (lowerNormalize p) < certThresholdVal lowerHistoryH5.threshold _ _
    rw [(threshold_values p).2.2.2.1]
    exact h5

private theorem mixed_3_cut (p : LowerPair) (h2 : ¬lowerH p 2) (h5 : lowerH p 5)
    (h6 : lowerH p 6) (h7 : lowerH p 7) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,
        lowerHistoryH7Mixed] := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH2.threshold _ _
    rw [(threshold_values p).2.2.1]; exact le_of_not_gt h2
  · change lowerScale (lowerNormalize p) < certThresholdVal lowerHistoryH5.threshold _ _
    rw [(threshold_values p).2.2.2.1]; exact h5
  · change lowerScale (lowerNormalize p) < certThresholdVal lowerHistoryH6.threshold _ _
    rw [(threshold_values p).2.2.2.2.1]; exact h6
  · change lowerScale (lowerNormalize p) < certThresholdVal lowerHistoryH7Mixed.threshold _ _
    rw [(threshold_values p).2.2.2.2.2.1]; exact h7

private theorem mixed_not2_not5_cut (p : LowerPair) (h2 : ¬lowerH p 2)
    (h5 : ¬lowerH p 5) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5] := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH2.threshold _ _
    rw [(threshold_values p).2.2.1]; exact le_of_not_gt h2
  · change certThresholdVal lowerHistoryH5.threshold _ _ ≤ lowerScale (lowerNormalize p)
    rw [(threshold_values p).2.2.2.1]; exact le_of_not_gt h5

private theorem mixed_not6_cut (p : LowerPair) (h2 : ¬lowerH p 2)
    (h5 : lowerH p 5) (h6 : ¬lowerH p 6) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,
        lowerHistoryComplement lowerHistoryH6] := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH2.threshold _ _
    rw [(threshold_values p).2.2.1]; exact le_of_not_gt h2
  · change lowerScale (lowerNormalize p) < certThresholdVal lowerHistoryH5.threshold _ _
    rw [(threshold_values p).2.2.2.1]; exact h5
  · change certThresholdVal lowerHistoryH6.threshold _ _ ≤ lowerScale (lowerNormalize p)
    rw [(threshold_values p).2.2.2.2.1]; exact le_of_not_gt h6

private theorem mixed_6_not7_cut (p : LowerPair) (h2 : ¬lowerH p 2)
    (h5 : lowerH p 5) (h6 : lowerH p 6) (h7 : ¬lowerH p 7) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,
        lowerHistoryComplement lowerHistoryH7Mixed] := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH2.threshold _ _
    rw [(threshold_values p).2.2.1]; exact le_of_not_gt h2
  · change lowerScale (lowerNormalize p) < certThresholdVal lowerHistoryH5.threshold _ _
    rw [(threshold_values p).2.2.2.1]; exact h5
  · change lowerScale (lowerNormalize p) < certThresholdVal lowerHistoryH6.threshold _ _
    rw [(threshold_values p).2.2.2.2.1]; exact h6
  · change certThresholdVal lowerHistoryH7Mixed.threshold _ _ ≤ lowerScale (lowerNormalize p)
    rw [(threshold_values p).2.2.2.2.2.1]; exact le_of_not_gt h7

private theorem mixed_special_cut (p : LowerPair) (h2 : ¬lowerH p 2)
    (h5 : ¬lowerH p 5) (h21 : ¬lowerH p 21) (h23 : lowerH p 23) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,
        lowerHistoryComplement lowerHistoryH21,lowerHistoryH23] := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH2.threshold _ _
    rw [(threshold_values p).2.2.1]; exact le_of_not_gt h2
  · change certThresholdVal lowerHistoryH5.threshold _ _ ≤ lowerScale (lowerNormalize p)
    rw [(threshold_values p).2.2.2.1]; exact le_of_not_gt h5
  · change certThresholdVal lowerHistoryH21.threshold _ _ ≤ lowerScale (lowerNormalize p)
    rw [(threshold_values p).2.2.2.2.2.2.1]; exact le_of_not_gt h21
  · change certThresholdVal lowerHistoryH23.threshold _ _ < lowerScale (lowerNormalize p)
    rw [(threshold_values p).2.2.2.2.2.2.2]; exact h23


private theorem late_mem_candidate (p : LowerPair) (l : LowerLabel)
    (h : l ∈ lowerLateList p) : l ∈ lowerLateCandidates := by
  unfold lowerLateList at h
  split at h
  · exact ((Classical.choose_spec ‹∃ ls, lowerLateRouteValid p ls›).1 l h).1
  · simp at h

private theorem offered_equal_two (p : LowerPair) (hm : ¬lowerMixed p)
    (ho : lowerOffered p ([2],[])) : lowerA p 3 ∨ lowerA p 9 := by
  by_contra h
  simp only [not_or] at h
  rcases ho with ho | ho
  · simp only [hm,if_false,lowerEqualList,h.1,h.2] at ho
    split_ifs at ho
    all_goals try { simp at ho }
    all_goals
      have hl : (([2],[]) : LowerLabel) ∈ lowerLateList p := by simpa using ho
      have hc := late_mem_candidate p ([2],[]) hl
      simp [lowerLateCandidates] at hc
  · rcases ho.2 with ⟨k,hk,heq⟩
    have := congrArg (fun z => z.2.length) heq
    simp at this
    omega


private theorem history_not_early (p : LowerPair) (l : LowerLabel) (hl : l ∈ lowerHistoryLabels) :
    ¬ l ∈ lowerEarlyList p := by
  intro h
  simp only [lowerHistoryLabels,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold lowerEarlyList at h
  all_goals split_ifs at h <;> simp_all

private theorem late_history_only (p : LowerPair) (l : LowerLabel) (hl : l ∈ lowerHistoryLabels)
    (h : l ∈ lowerLateList p) : l = ([2],[1]) := by
  have hc := late_mem_candidate p l h
  simp only [lowerHistoryLabels,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [lowerLateCandidates] at hc ⊢

private theorem history_not_run (l : LowerLabel) (hl : l ∈ lowerHistoryLabels) :
    ¬ ∃ k : ℕ, 0 < k ∧ l = (List.replicate k 3,List.replicate k 3) := by
  intro h
  rcases h with ⟨k,hk,heq⟩
  rcases k with _ | k
  · omega
  simp only [lowerHistoryLabels,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at heq
  all_goals
    have hh := congrArg List.head? heq.2
    simp [List.replicate_succ] at hh

private theorem offered_equal_three (p : LowerPair) (hm : ¬lowerMixed p)
    (ho : lowerOffered p ([3],[])) : lowerA p 3 := by
  by_contra h3
  rcases ho with ho | ho
  · simp only [hm,if_false,lowerEqualList,h3] at ho
    split_ifs at ho
    all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ho
    all_goals norm_num at ho
    all_goals try {exact history_not_early p ([3],[]) (by simp [lowerHistoryLabels]) ho}
    all_goals try {cases ho}
    all_goals have hh := late_history_only p ([3],[]) (by simp [lowerHistoryLabels]) ho
    all_goals simp at hh
  · exact history_not_run ([3],[]) (by simp [lowerHistoryLabels]) ho.2

private theorem offered_equal_two_one (p : LowerPair) (hm : ¬lowerMixed p)
    (ho : lowerOffered p ([2],[1])) : ¬lowerA p 3 ∧ ¬lowerA p 9 := by
  constructor
  · intro h3
    rcases ho with ho | ho
    · simp [hm,lowerEqualList,h3] at ho
    · exact history_not_run ([2],[1]) (by simp [lowerHistoryLabels]) ho.2
  · intro h9
    rcases ho with ho | ho
    · simp only [hm,if_false,lowerEqualList,h9] at ho
      split_ifs at ho
      all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ho
      all_goals norm_num at ho
      all_goals exact history_not_early p ([2],[1]) (by simp [lowerHistoryLabels]) ho
    · exact history_not_run ([2],[1]) (by simp [lowerHistoryLabels]) ho.2

private theorem offered_equal_three_one (p : LowerPair) (hm : ¬lowerMixed p)
    (ho : lowerOffered p ([3],[1])) : ¬lowerA p 3 ∧ ¬lowerA p 9 := by
  constructor
  · intro h3
    rcases ho with ho | ho
    · simp [hm,lowerEqualList,h3] at ho
    · exact history_not_run ([3],[1]) (by simp [lowerHistoryLabels]) ho.2
  · intro h9
    rcases ho with ho | ho
    · simp only [hm,if_false,lowerEqualList,h9] at ho
      split_ifs at ho
      all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ho
      all_goals norm_num at ho
      all_goals try {exact history_not_early p ([3],[1]) (by simp [lowerHistoryLabels]) ho}
      all_goals have hh := late_history_only p ([3],[1]) (by simp [lowerHistoryLabels]) ho
      all_goals simp at hh
    · exact history_not_run ([3],[1]) (by simp [lowerHistoryLabels]) ho.2

private theorem not_offered_equal_nil_one (p : LowerPair) (hm : ¬lowerMixed p) :
    ¬lowerOffered p ([],[1]) := by
  intro ho
  rcases ho with ho | ho
  · simp only [hm,if_false,lowerEqualList] at ho
    split_ifs at ho
    all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ho
    all_goals norm_num at ho
    all_goals try {exact history_not_early p ([],[1]) (by simp [lowerHistoryLabels]) ho}
    all_goals have hh := late_history_only p ([],[1]) (by simp [lowerHistoryLabels]) ho
    all_goals simp at hh
  · exact history_not_run ([],[1]) (by simp [lowerHistoryLabels]) ho.2


private theorem offered_mixed_mem (p : LowerPair) (l : LowerLabel)
    (hl : l ∈ lowerHistoryLabels) (hm : lowerMixed p) (ho : lowerOffered p l) :
    l ∈ lowerMixedList p := by
  rcases ho with ho | ho
  · simpa [hm] using ho
  · exact (history_not_run l hl ho.2).elim

private theorem offered_mixed_two (p : LowerPair) (hm : lowerMixed p)
    (ho : lowerOffered p ([2],[])) : ¬lowerH p 2 ∧ lowerH p 5 := by
  have h := offered_mixed_mem p ([2],[]) (by simp [lowerHistoryLabels]) hm ho
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all

private theorem offered_mixed_three (p : LowerPair) (hm : lowerMixed p)
    (ho : lowerOffered p ([3],[])) :
    ¬lowerH p 2 ∧ lowerH p 5 ∧ lowerH p 6 ∧ lowerH p 7 := by
  have h := offered_mixed_mem p ([3],[]) (by simp [lowerHistoryLabels]) hm ho
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all

private theorem offered_mixed_two_one (p : LowerPair) (hm : lowerMixed p)
    (ho : lowerOffered p ([2],[1])) : ¬lowerH p 2 ∧ ¬lowerH p 5 := by
  have h := offered_mixed_mem p ([2],[1]) (by simp [lowerHistoryLabels]) hm ho
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all

private theorem offered_mixed_nil_one (p : LowerPair) (hm : lowerMixed p)
    (ho : lowerOffered p ([],[1])) :
    lowerH p 2 ∨ (¬lowerH p 2 ∧ ¬lowerH p 5 ∧ ¬lowerH p 21 ∧
      ¬lowerEnds (lowerNormalize p).2 [3] ∧ lowerH p 23) := by
  have h := offered_mixed_mem p ([],[1]) (by simp [lowerHistoryLabels]) hm ho
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all

private theorem offered_mixed_three_one (p : LowerPair) (hm : lowerMixed p)
    (ho : lowerOffered p ([3],[1])) :
    (¬lowerH p 2 ∧ lowerH p 5 ∧ ¬lowerH p 6) ∨
    (¬lowerH p 2 ∧ lowerH p 5 ∧ lowerH p 6 ∧ ¬lowerH p 7) ∨
    (¬lowerH p 2 ∧ ¬lowerH p 5 ∧ ¬lowerL p) := by
  have h := offered_mixed_mem p ([3],[1]) (by simp [lowerHistoryLabels]) hm ho
  unfold lowerMixedList at h
  split_ifs at h <;> simp_all
  all_goals by_cases hh : lowerH p 6 <;> simp_all


private theorem mixed_h2_cut (p : LowerPair) (h2 : lowerH p 2) :
    lowerHistoryAtBase (lowerNormalize p) [lowerHistoryH2] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  subst b
  change certThresholdVal lowerHistoryH2.threshold _ _ < lowerScale (lowerNormalize p)
  rw [(threshold_values p).2.2.1]
  exact h2

end Choices15


open Freiman
namespace Choices15

private theorem source_choices_core : LowerHistoryChoiceLaw := by
  intro base s l hc hn hl ho
  rw [← hn]
  have hp := mixed_iff_context_parity_ne base s.context hc
  simp only [lowerHistoryLabels,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨[], ?_, ?_⟩
    · simp [lowerHistorySourceChoices]
    · simp [lowerHistoryAtBase,lowerHistoryConditions]
  · by_cases heq : s.context.parity.1 = s.context.parity.2
    · have hm : ¬lowerMixed base := hp.not.mpr (not_ne_iff.mpr heq)
      rcases offered_equal_two base hm ho with h3 | h9
      · refine ⟨[lowerHistoryComplement lowerHistoryH7], ?_, a3_cut base h3⟩
        simp [lowerHistorySourceChoices,heq]
      · by_cases h3 : lowerA base 3
        · refine ⟨[lowerHistoryComplement lowerHistoryH7], ?_, a3_cut base h3⟩
          simp [lowerHistorySourceChoices,heq]
        · refine ⟨[lowerHistoryH7,lowerHistoryH9], ?_, not_a3_a9_cut base h3 h9⟩
          simp [lowerHistorySourceChoices,heq]
    · have hm : lowerMixed base := hp.mpr heq
      obtain ⟨h2,h5⟩ := offered_mixed_two base hm ho
      refine ⟨[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5], ?_,
        mixed_2_cut base h2 h5⟩
      simp [lowerHistorySourceChoices,heq]
  · by_cases heq : s.context.parity.1 = s.context.parity.2
    · have hm : ¬lowerMixed base := hp.not.mpr (not_ne_iff.mpr heq)
      have h3 := offered_equal_three base hm ho
      refine ⟨[lowerHistoryComplement lowerHistoryH7], ?_, a3_cut base h3⟩
      simp [lowerHistorySourceChoices,heq]
    · have hm : lowerMixed base := hp.mpr heq
      obtain ⟨h2,h5,h6,h7⟩ := offered_mixed_three base hm ho
      refine ⟨[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,
        lowerHistoryH6,lowerHistoryH7Mixed], ?_,mixed_3_cut base h2 h5 h6 h7⟩
      simp [lowerHistorySourceChoices,heq]
  · by_cases heq : s.context.parity.1 = s.context.parity.2
    · exact (not_offered_equal_nil_one base (hp.not.mpr (not_ne_iff.mpr heq)) ho).elim
    · have hm : lowerMixed base := hp.mpr heq
      rcases offered_mixed_nil_one base hm ho with h2 | hs
      · refine ⟨[lowerHistoryH2], ?_,mixed_h2_cut base h2⟩
        simp [lowerHistorySourceChoices,heq]
      · obtain ⟨h2,h5,h21,he,h23⟩ := hs
        have hsuf : ¬([3] : List ℕ+).IsSuffix
            (lowerHistoryPick s.context.words (!s.wider)) := by
          rwa [← norm_second_three_iff base s.context s.wider hc hn]
        refine ⟨[lowerHistoryComplement lowerHistoryH2,
          lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,
          lowerHistoryH23], ?_,mixed_special_cut base h2 h5 h21 h23⟩
        simp [lowerHistorySourceChoices,heq,hsuf]
  · by_cases heq : s.context.parity.1 = s.context.parity.2
    · have hm : ¬lowerMixed base := hp.not.mpr (not_ne_iff.mpr heq)
      obtain ⟨h3,h9⟩ := offered_equal_two_one base hm ho
      refine ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9], ?_,
        not_a3_not_a9_cut base h3 h9⟩
      simp [lowerHistorySourceChoices,heq]
    · have hm : lowerMixed base := hp.mpr heq
      obtain ⟨h2,h5⟩ := offered_mixed_two_one base hm ho
      refine ⟨[lowerHistoryComplement lowerHistoryH2,
        lowerHistoryComplement lowerHistoryH5], ?_,mixed_not2_not5_cut base h2 h5⟩
      simp [lowerHistorySourceChoices,heq]
  · by_cases heq : s.context.parity.1 = s.context.parity.2
    · have hm : ¬lowerMixed base := hp.not.mpr (not_ne_iff.mpr heq)
      obtain ⟨h3,h9⟩ := offered_equal_three_one base hm ho
      refine ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9], ?_,
        not_a3_not_a9_cut base h3 h9⟩
      simp [lowerHistorySourceChoices,heq]
    · have hm : lowerMixed base := hp.mpr heq
      rcases offered_mixed_three_one base hm ho with hs | hs | hs
      · obtain ⟨h2,h5,h6⟩ := hs
        refine ⟨[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,
          lowerHistoryComplement lowerHistoryH6], ?_,mixed_not6_cut base h2 h5 h6⟩
        simp [lowerHistorySourceChoices,heq]
      · obtain ⟨h2,h5,h6,h7⟩ := hs
        refine ⟨[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,
          lowerHistoryComplement lowerHistoryH7Mixed], ?_,
          mixed_6_not7_cut base h2 h5 h6 h7⟩
        simp [lowerHistorySourceChoices,heq]
      · obtain ⟨h2,h5,hL⟩ := hs
        have hsuf : ¬([3,1] : List ℕ+).IsSuffix
            (lowerHistoryPick s.context.words s.wider) := by
          rwa [← norm_first_31_iff base s.context s.wider hc hn]
        refine ⟨[lowerHistoryComplement lowerHistoryH2,
          lowerHistoryComplement lowerHistoryH5], ?_,mixed_not2_not5_cut base h2 h5⟩
        simp [lowerHistorySourceChoices,heq,hsuf]

end Choices15

theorem solution :
    LowerHistoryChoiceLaw := by
  exact Choices15.source_choices_core

#print axioms solution
