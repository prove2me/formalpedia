-- Prove2me | solution 1 for Freiman.lowerHistory_reached_choices
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T14:06:17.555544+00:00
-- url     : https://prove2.me/submissions/acadd528-19b4-47d0-9dd0-06e6f33e7b2a

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

private theorem _root_.Freiman.lowerHistory_source_choices : LowerHistoryChoiceLaw := by
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


open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ReachedChoices15

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

private theorem replay_tie_state_parity (base : LowerPair) (p : LowerHistoryPath) (j : ℕ)
    (hbase : base.1.length % 2 = base.2.length % 2)
    (htie : (lowerHistoryReplay base p j).1.1 =
      (lowerHistoryReplay base p j).1.2) :
    (lowerHistoryStateAt p j).context.parity.1 =
      (lowerHistoryStateAt p j).context.parity.2 := by
  have happ := replay_append base p j
  have h₁ := congrArg (fun z : LowerPair => z.1.length) happ.1
  have h₂ := congrArg (fun z : LowerPair => z.2.length) happ.1
  have ht := congrArg List.length htie
  have hm :
      (lowerHistoryReplay ([],[]) p j).1.1.length % 2 =
        (lowerHistoryReplay ([],[]) p j).1.2.length % 2 := by
    simp only [lowerHistoryAppend,List.length_append,Prod.fst,Prod.snd] at h₁ h₂
    omega
  rw [(state_replay_shape p j).1]
  simp only [Prod.fst,Prod.snd]
  rw [hm]


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
  · exact (not_le.mp h).le

private theorem normalize_idem (p : LowerPair) : lowerNormalize (lowerNormalize p) = lowerNormalize p := by
  conv_lhs => rw [lowerNormalize]
  exact if_pos (normalize_wide p)

private theorem sourceChoices_orient (s : LowerHistoryState) (l : LowerLabel) :
    lowerHistorySourceChoices
      ⟨⟨lowerHistoryOrient s.context.words s.wider,
          if s.wider then (s.context.parity.2,s.context.parity.1) else s.context.parity⟩,
        false,s.markedDone,s.previous⟩ l = lowerHistorySourceChoices s l := by
  rcases s with ⟨⟨⟨u,v⟩,⟨a,b⟩⟩,w,m,pr⟩
  cases w
  · simp [lowerHistorySourceChoices,lowerHistoryOrient,lowerHistoryPick]
  · cases a <;> cases b <;>
      simp [lowerHistorySourceChoices,lowerHistoryOrient,lowerHistoryPick]

private theorem pull_list (hpull : LowerHistoryPullLaw)
    (base words : LowerPair) (flip : Bool) (bs : List CertBound)
    (hf : ∀ b ∈ bs, 0 < certFieldVal b.threshold.c ∧
      0 ≤ certFieldVal b.threshold.x0 ∧ 0 ≤ certFieldVal b.threshold.x1 ∧
      0 ≤ certFieldVal b.threshold.y0 ∧ 0 ≤ certFieldVal b.threshold.y1)
    (hbs : lowerHistoryAtBase (lowerHistoryOrient (lowerHistoryAppend base words) flip) bs) :
    lowerHistoryAtBase base (bs.map fun b => lowerHistoryPull b words flip) := by
  intro b hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  have hv := hf a ha
  have haone : lowerHistoryAtBase
      (lowerHistoryOrient (lowerHistoryAppend base words) flip) [a] := by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    exact hbs a ha
  have hout :=
    (hpull base words a flip hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2).mp haone
  exact hout _ (by simp)


private theorem legal_at : ∀ (steps : List (LowerLabel × Bool))
    (s : LowerHistoryState) (i : ℕ) (l : LowerLabel) (reflect : Bool),
    lowerHistoryLegalSteps s steps → steps[i]? = some (l,reflect) →
    lowerHistoryStepLegal
      ((steps.take i).foldl (fun z step => lowerHistoryAdvance z step.1 step.2) s)
      l reflect := by
  intro steps
  induction steps with
  | nil => intro s i l reflect hs hg; simp at hg
  | cons a tail ih =>
      intro s i l reflect hs hg
      rcases hs with ⟨ha,ht⟩
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hg
          rcases a with ⟨al,ar⟩
          simp only [List.take_zero, List.foldl_nil]
          cases hg
          exact ha
      | succ i =>
          simp only [List.getElem?_cons_succ] at hg
          simp only [List.take_succ_cons, List.foldl_cons]
          exact ih (lowerHistoryAdvance s a.1 a.2) i l reflect ht hg

private theorem threshold_normalize (p : LowerPair) (c : ℝ) (i j k l : ℕ) :
    lowerThreshold (lowerNormalize p) c i j k l = lowerThreshold p c i j k l := by
  simp only [lowerThreshold, normalize_idem]

private theorem A_normalize (p : LowerPair) (i : ℕ) :
    lowerA (lowerNormalize p) i ↔ lowerA p i := by
  unfold lowerA
  rw [normalize_idem]
  simp only [threshold_normalize]

private theorem H_normalize (p : LowerPair) (i : ℕ) :
    lowerH (lowerNormalize p) i ↔ lowerH p i := by
  unfold lowerH
  rw [normalize_idem]
  simp only [threshold_normalize]

private theorem mixed_normalize (p : LowerPair) :
    lowerMixed (lowerNormalize p) ↔ lowerMixed p := by
  unfold lowerMixed lowerNormalize
  split_ifs
  · rfl
  · constructor <;> intro h h' <;> exact h h'.symm

private theorem ends_normalize (p : LowerPair) :
    lowerL (lowerNormalize p) = lowerL p ∧ lowerR (lowerNormalize p) = lowerR p ∧
    lowerLStar (lowerNormalize p) = lowerLStar p ∧
    lowerRStar (lowerNormalize p) = lowerRStar p := by
  simp only [lowerL,lowerR,lowerLStar,lowerRStar,normalize_idem]
  simp

private theorem early_normalize (p : LowerPair) :
    lowerEarlyList (lowerNormalize p) = lowerEarlyList p := by
  unfold lowerEarlyList
  simp only [A_normalize]

private theorem late_valid_normalize (p : LowerPair) (ls : List LowerLabel) :
    lowerLateRouteValid (lowerNormalize p) ls ↔ lowerLateRouteValid p ls := by
  simp only [lowerLateRouteValid,lowerChild,normalize_idem]

private theorem late_normalize (p : LowerPair) :
    lowerLateList (lowerNormalize p) = lowerLateList p := by
  unfold lowerLateList
  by_cases h : ∃ ls, lowerLateRouteValid p ls
  · have hn : ∃ ls, lowerLateRouteValid (lowerNormalize p) ls := by simpa only [late_valid_normalize]
    simp only [h,hn,dite_true]
    congr 1
    funext ls
    apply propext
    exact late_valid_normalize p ls
  · have hn : ¬ ∃ ls, lowerLateRouteValid (lowerNormalize p) ls := by simpa only [late_valid_normalize]
    simp only [h,hn,dite_false]

private theorem mixedList_normalize (p : LowerPair) :
    lowerMixedList (lowerNormalize p) = lowerMixedList p := by
  unfold lowerMixedList
  rw [normalize_idem]
  rw [ends_normalize p |>.1, ends_normalize p |>.2.2.1, ends_normalize p |>.2.2.2]
  simp only [H_normalize]

private theorem equalList_normalize (p : LowerPair) :
    lowerEqualList (lowerNormalize p) = lowerEqualList p := by
  unfold lowerEqualList
  rw [ends_normalize p |>.1, ends_normalize p |>.2.1,
    ends_normalize p |>.2.2.1, ends_normalize p |>.2.2.2]
  simp only [A_normalize,early_normalize,late_normalize]

private theorem run_normalize (p : LowerPair) :
    lowerRunOffered (lowerNormalize p) ↔ lowerRunOffered p := by
  unfold lowerRunOffered
  simp only [mixed_normalize,A_normalize,ends_normalize,normalize_idem]

private theorem offered_normalize (p : LowerPair) (l : LowerLabel) :
    lowerOffered (lowerNormalize p) l ↔ lowerOffered p l := by
  simp only [lowerOffered,mixed_normalize,mixedList_normalize,equalList_normalize,
    run_normalize]

private theorem normalize_reflect (p : LowerPair) :
    lowerNormalize p = lowerHistoryOrient p (lowerReflects p) := by
  unfold lowerNormalize lowerReflects lowerHistoryOrient
  by_cases h : lowerWidth p.1 < lowerWidth p.2
  · simp [h, not_le_of_gt h]
  · simp [h, le_of_not_gt h]

private theorem replay_succ (base : LowerPair) (p : LowerHistoryPath) (i : ℕ)
    (l : LowerLabel) (reflect : Bool) (hget : p.steps[i]? = some (l,reflect)) :
    lowerHistoryReplay base p (i+1) =
      let r := lowerHistoryReplay base p i
      (lowerHistoryRawStep r.1 r.2 l, if reflect then !r.2 else r.2) := by
  unfold lowerHistoryReplay
  rw [List.take_succ, hget]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem raw_child (r : LowerPair) (wide : Bool) (l : LowerLabel)
    (hn : lowerNormalize (lowerHistoryOrient r wide) = lowerHistoryOrient r wide) :
    lowerHistoryRawStep r wide l =
      lowerHistoryOrient (lowerChild (lowerHistoryOrient r wide) l) wide := by
  cases wide
  · simp only [lowerHistoryOrient, Bool.false_eq_true, if_false] at hn
    simp [lowerHistoryRawStep,lowerHistoryOrient,lowerChild,hn]
  · simp only [lowerHistoryOrient, if_true] at hn
    simp [lowerHistoryRawStep,lowerHistoryOrient,lowerChild,hn]

private theorem child_injective (p : LowerPair) : Function.Injective (lowerChild p) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  simp only [lowerChild] at h
  injection h with h₁ h₂
  have h₁' : a.reverse = c.reverse := List.append_right_injective _ h₁
  have h₂' : b = d := List.append_right_injective _ h₂
  have h₁'' : a = c := by simpa using congrArg List.reverse h₁'
  exact Prod.ext h₁'' h₂'

private theorem late_mem_candidates (p : LowerPair) (l : LowerLabel)
    (hl : l ∈ lowerLateList p) : l ∈ lowerLateCandidates := by
  unfold lowerLateList at hl
  split at hl
  next hex => exact (Classical.choose_spec hex).1 l hl |>.1
  next => simp at hl

private def labelShape (l : LowerLabel) : Prop :=
  l.1 ≠ [] ∧ (l.1 = [1] → l.2 ≠ [2] ∧ l.2 ≠ [3])

private theorem late_shape (p : LowerPair) (l : LowerLabel)
    (hl : l ∈ lowerLateList p) : labelShape l := by
  have hc := late_mem_candidates p l hl
  simp only [lowerLateCandidates,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [labelShape]

private theorem early_shape (p : LowerPair) (l : LowerLabel)
    (hl : l ∈ lowerEarlyList p) : labelShape l := by
  unfold lowerEarlyList at hl
  split_ifs at hl <;>
    simp_all only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  all_goals aesop (add simp [labelShape])

private theorem equal_shape (p : LowerPair) (l : LowerLabel)
    (hl : l ∈ lowerEqualList p) : labelShape l := by
  unfold lowerEqualList at hl
  split_ifs at hl <;>
    simp_all only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  all_goals
    aesop (add safe forward early_shape) (add safe forward late_shape)
      (add simp [labelShape])

private theorem offered_equal_shape (w : List ℕ+) (a : LowerLabel)
    (ha : lowerOffered (w,w) a) : labelShape a := by
  rcases ha with ha | ⟨_,k,hk,rfl⟩
  · apply equal_shape (w,w) a
    simpa [lowerMixed] using ha
  · cases k with
    | zero => omega
    | succ k => simp [labelShape,List.replicate_succ]

private theorem swapped_child_impossible (w : List ℕ+) (a l : LowerLabel)
    (hl : l ∈ lowerHistoryLabels) (hln : l.1 ≠ [])
    (ha : lowerOffered (w,w) a)
    (he : (lowerChild (w,w) a).swap = lowerChild (w,w) l) : False := by
  have hs := offered_equal_shape w a ha
  simp only [lowerHistoryLabels,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [lowerChild,lowerNormalize] at he
  all_goals try { exact hln rfl }
  all_goals
    have hae : a = (_,_) := Prod.ext he.2 he.1
    subst a
    simp [labelShape] at hs

private theorem actual_label_at_step (t : ℝ) (h : ℕ → LowerPair) (n start : ℕ)
    (base : LowerPair) (flip : Bool) (p : LowerHistoryPath)
    (hh : lowerHistory t h n) (hlen : start + p.steps.length = n)
    (hreal : lowerHistoryRealizes h start base flip p)
    (hp : lowerHistoryStructural p) (j : ℕ) (hj : j < p.steps.length)
    (l : LowerLabel) (reflect : Bool) (hget : p.steps[j]? = some (l,reflect)) :
    ∀ a : LowerLabel, lowerOffered (h (start+j)) a →
      h (start+j+1) = lowerChild (h (start+j)) a → a = l := by
  intro a ha hnext
  let r := lowerHistoryReplay base p j
  let q := lowerNormalize (h (start+j))
  have hrj := hreal.2.2.2 j hj.le
  have hrn := hreal.2.2.2 (j+1) (by omega)
  have hrs := replay_succ base p j l reflect hget
  have hq : q = lowerHistoryOrient r.1 r.2 := by simpa [q,r] using hrj.2.2
  have hraw : lowerHistoryRawStep r.1 r.2 l =
      lowerHistoryOrient (lowerChild q l) r.2 := by
    rw [hq]
    apply raw_child
    rw [← hq]
    simpa only [q] using normalize_idem (h (start+j))
  have hfixed : lowerNormalize (lowerHistoryOrient r.1 r.2) =
      lowerHistoryOrient r.1 r.2 := by
    rw [← hq]
    simpa only [q] using normalize_idem (h (start+j))
  have hnext' : h (start+j+1) = lowerChild q a := by
    simpa only [q,lowerChild,normalize_idem] using hnext
  have hcur := hrj.1
  have hnor := hrj.2.2
  have hnxt := hrn.1
  rw [show start + (j+1) = start+j+1 by omega] at hnxt
  simp only [r] at hraw
  rw [hrs] at hnxt
  simp only at hnxt
  unfold lowerPhysicalPath at hnxt
  rw [hnext'] at hnxt
  cases ho : lowerOrientation h (start+j) <;>
    cases hf : flip <;>
    cases hw : (lowerHistoryReplay base p j).2 <;>
    cases hhf : lowerReflects (h (start+j))
  all_goals
    simp [lowerPhysicalPath,lowerOrientation,ho,hf,hw,hhf,lowerHistoryOrient,
      normalize_reflect] at hcur hnor hnxt hraw
  all_goals have he := hnxt.trans hraw
  all_goals try {
    apply child_injective q
    exact he }
  all_goals try {
    apply child_injective q
    apply Prod.ext
    · exact congrArg Prod.snd he
    · exact congrArg Prod.fst he }
  all_goals
    have hlegal := legal_at p.steps (lowerHistoryInitialState p) j l reflect hp.2.2.1 hget
    have hphys : h (start+j) = (lowerHistoryReplay base p j).1 := by
      apply Prod.ext <;> aesop
    rw [hphys] at hcur hnor ha
    have htie : (lowerHistoryReplay base p j).1.1 =
        (lowerHistoryReplay base p j).1.2 := by
      first
      | exact (congrArg Prod.fst hnor).symm
      | exact congrArg Prod.fst hnor
      | exact (congrArg Prod.fst hcur).symm
      | exact congrArg Prod.fst hcur
    have hpeq := replay_tie_state_parity base p j hreal.2.2.1 htie
    have hln : l.1 ≠ [] := by
      intro hl0
      exact hlegal.2.1 hl0 hpeq
    exfalso
    let w := (lowerHistoryReplay base p j).1.1
    have hrp : (lowerHistoryReplay base p j).1 = (w,w) := by
      apply Prod.ext
      · rfl
      · exact htie.symm
    have hqr : q = (lowerHistoryReplay base p j).1 := by
      rw [hq]
      simp only [r]
      rw [hrp]
      cases (lowerHistoryReplay base p j).2 <;> rfl
    rw [hrp] at ha
    rw [hqr,hrp] at he
    apply swapped_child_impossible w a l hlegal.1 hln ha
    first
    | exact he
    | simpa [Prod.swap] using congrArg Prod.swap he


private theorem offered_at_step (t : ℝ) (h : ℕ → LowerPair) (n start : ℕ)
    (base : LowerPair) (flip : Bool) (p : LowerHistoryPath)
    (hh : lowerHistory t h n) (hlen : start + p.steps.length = n)
    (hreal : lowerHistoryRealizes h start base flip p)
    (hp : lowerHistoryStructural p) (j : ℕ) (hj : j < p.steps.length)
    (l : LowerLabel) (reflect : Bool) (hget : p.steps[j]? = some (l,reflect)) :
    lowerOffered (lowerNormalize (h (start+j))) l := by
  obtain ⟨a,ha,_hpri,hnext⟩ := hh.2.2 (start+j) (by omega)
  have hal := actual_label_at_step t h n start base flip p hh hlen hreal hp j hj
    l reflect hget a ha (by simpa [Nat.add_assoc] using hnext)
  subst a
  exact (offered_normalize (h (start+j)) l).2 ha

private theorem reached_choices_core (hc : LowerHistoryChoiceLaw) (hpull : LowerHistoryPullLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p)
    (hr : lowerHistoryReached t h n base p) : lowerHistoryChoiceEvents base p := by
  rcases hr with ⟨start,flip,hlen,hreal,hsource⟩
  intro j l reflect hget
  have hj : j < p.steps.length := List.getElem?_eq_some_iff.mp hget |>.1
  let words := lowerHistoryWordsAt p j
  let s := lowerHistoryStateAt p j
  let q := lowerHistoryOrient (lowerHistoryAppend base words) s.wider
  let ss : LowerHistoryState :=
    ⟨⟨lowerHistoryOrient s.context.words s.wider,
       if s.wider then (s.context.parity.2,s.context.parity.1) else s.context.parity⟩,
      false,s.markedDone,s.previous⟩
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
  have hctx : lowerHistoryContextFits q ss.context := by
    exact reached_state_context base p j hreal.1 hbase2 hreal.2.2.1
  have hrj := hreal.2.2.2 j hj.le
  have hq : q = lowerNormalize (h (start+j)) := by
    have happ := replay_append base p j
    have hshape := state_replay_shape p j
    calc
      q = lowerHistoryOrient (lowerHistoryReplay base p j).1
          (lowerHistoryReplay base p j).2 := by
        dsimp only [q]
        rw [hshape.2, ← happ.2]
        congr 1
        exact happ.1.symm
      _ = lowerNormalize (h (start+j)) := hrj.2.2.symm
  have hnorm : lowerNormalize q = lowerHistoryOrient q ss.wider := by
    simp only [ss, lowerHistoryOrient, Bool.false_eq_true, if_false]
    rw [hq, normalize_idem]
  have hlegal : lowerHistoryStepLegal s l reflect := by
    exact legal_at p.steps (lowerHistoryInitialState p) j l reflect hp.2.2.1 hget
  have hl : l ∈ lowerHistoryLabels := by
    simpa only [lowerHistoryStepLegal] using hlegal.1
  have hoff : lowerOffered q l := by
    rw [hq]
    exact offered_at_step t h n start base flip p hh hlen hreal hp j hj l reflect hget
  obtain ⟨bs,hbsmem,hbs⟩ := hc q ss l hctx hnorm hl hoff
  have hbsmem' : bs ∈ lowerHistorySourceChoices s l := by
    rw [← sourceChoices_orient s l]
    exact hbsmem
  refine ⟨bs,hbsmem',?_⟩
  apply pull_list hpull base words s.wider bs
  · intro b hb
    exact Choices15.source_choice_fields s l bs hbsmem' b hb
  · simpa [q,ss,lowerHistoryOrient] using hbs

end ReachedChoices15

open Freiman

private theorem reached_choices_complete (hc : LowerHistoryChoiceLaw)
    (hpull : LowerHistoryPullLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) (base : LowerPair) (p : LowerHistoryPath)
    (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryChoiceEvents base p := by
  exact ReachedChoices15.reached_choices_core hc hpull t h n hh base p hp hr


theorem solution (hc : LowerHistoryChoiceLaw) (hpull : LowerHistoryPullLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryChoiceEvents base p := by
  exact reached_choices_complete hc hpull t h n hh base p hp hr

#print axioms solution
