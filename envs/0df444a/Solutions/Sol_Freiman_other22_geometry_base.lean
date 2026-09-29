-- Prove2me | solution 1 for Freiman.other22_geometry_base
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-15T20:20:33.995565+00:00
-- url     : https://prove2.me/submissions/564aa79f-874b-41cd-ac6d-71fbf7331e39

import Definitions.Def_Freiman_other22Verification
import Theorems.Thm_Freiman_lowerHistory_goodness_semantics
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lowerHistory_theta_values
import Mathlib.Tactic

open Freiman
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem threshold_value (c : CertField) (i j k l : ℕ) (r s : ℝ) :
    certThresholdVal (lowerHistoryPB c i j k l false false).threshold r s =
    certFieldVal c * ((1+s*certFieldVal (lowerHistoryTheta j)) *
      (1+s*certFieldVal (lowerHistoryTheta l))) /
      ((1+r*certFieldVal (lowerHistoryTheta i)) *
      (1+r*certFieldVal (lowerHistoryTheta k))) := by
  simp only [lowerHistoryPB, lowerHistoryThreshold, lowerHistorySort]
  split_ifs <;> simp [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

private theorem source_tests (B : LowerPair) (hn : lowerNormalize B = B) :
    (lowerHistoryAtBase B [lowerHistoryComplement lowerHistoryH7] ↔ lowerA B 3) ∧
    (lowerHistoryAtBase B [lowerHistoryH7] ↔ ¬ lowerA B 3) ∧
    (lowerHistoryAtBase B [lowerHistoryH9] ↔ lowerA B 9) := by
  have h7 := threshold_value (lowerHistoryRat (31/100)) 3 63 25 66
    (lowerRatio B.1) (lowerRatio B.2)
  have h9 := threshold_value (⟨3/2,-1/2,0,0⟩ : CertField) 36 63 63 66
    (lowerRatio B.1) (lowerRatio B.2)
  simp only [lowerHistoryPB] at h7 h9
  simp only [lowerHistory_theta_values 3 (by simp), lowerHistory_theta_values 25 (by simp),
    lowerHistory_theta_values 36 (by simp), lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 66 (by simp)] at h7 h9
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton, forall_eq,
    lowerHistoryComplement, lowerHistoryH7, lowerHistoryH9, certBoundHolds,
    lowerHistoryPB, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true]
  rw [h7, h9]
  norm_num [lowerA, lowerThreshold, hn, lowerHistoryRat, certFieldVal]
  have he : (3/2 + -(1/2 * Real.sqrt 3) : ℝ) = (3-Real.sqrt 3)/2 := by ring
  rw [he]

private theorem final_bounds (S : LowerPair) (hn : lowerNormalize S = S)
    (h3 : ¬ lowerA S 3) (h9 : ¬ lowerA S 9) :
    lowerHistoryAtBase S [lowerHistoryH7, lowerHistoryComplement lowerHistoryH9, lowerHistoryHN] := by
  have ht := source_tests S hn
  have hfirst := ht.2.1.mpr h3
  have hsecond : lowerHistoryAtBase S [lowerHistoryComplement lowerHistoryH9] := by
    have hh : ¬ lowerHistoryAtBase S [lowerHistoryH9] := fun hx => h9 (ht.2.2.mp hx)
    simpa [lowerHistoryAtBase, lowerHistoryConditions, lowerHistoryComplement,
      certBoundHolds, lowerHistoryH9, lowerHistoryPB] using hh
  have hw : lowerWidth S.2 ≤ lowerWidth S.1 := by
    have h : lowerWidth (lowerNormalize S).2 ≤ lowerWidth (lowerNormalize S).1 := by
      unfold lowerNormalize
      split_ifs with h
      · exact h
      · exact le_of_not_ge h
    simpa [hn] using h
  have hnormal : lowerHistoryAtBase S [lowerHistoryHN] := by
    simpa [lowerHistoryHN] using (lowerHistory_width_threshold S ([],[])).1.mp
      (by simpa using hw)
  simpa [lowerHistoryAtBase, lowerHistoryConditions] using And.intro hfirst (And.intro hsecond hnormal)

private theorem scale_positive (Z : LowerPair) (hb : lowerParameterBox Z) :
    0 < lowerScale Z := by
  have h1 : (lowerCD Z.1).2 ≠ 0 := by
    intro he
    have hh := hb.1
    norm_num [lowerRatio, he] at hh
  have h2 : (lowerCD Z.2).2 ≠ 0 := by
    intro he
    have hh := hb.2.2.1
    norm_num [lowerRatio, he] at hh
  have hp1 : (0:ℝ) < (lowerCD Z.1).2 := by exact_mod_cast Nat.pos_of_ne_zero h1
  have hp2 : (0:ℝ) < (lowerCD Z.2).2 := by exact_mod_cast Nat.pos_of_ne_zero h2
  unfold lowerScale
  positivity

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryBaseEvent Z (other22Paths k) := by
  obtain ⟨good,hgood,hholds⟩ := lowerHistory_goodness_semantics Z (other22Context k)
    hc h.normalizedZ h.goodZ
  have hcuts := final_bounds Z h.normalizedZ h.largeZ3 h.largeZ9
  have hzero : lowerHistoryAtBase Z [lowerHistoryZero] := by
    have hp := scale_positive Z h.boxZ
    simpa [lowerHistoryAtBase, lowerHistoryConditions, lowerHistoryZero,
      lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryRat,
      certBoundHolds, certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal] using hp
  refine ⟨[lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,
    lowerHistoryComplement lowerHistoryH9] ++ good, ?_, ?_⟩
  · have hcat : (other22Paths k).catalog ≠ .initial := by fin_cases k <;> decide
    simp only [lowerHistoryBasePremises, if_neg hcat]
    change (lowerHistoryRelaxedGoodness (other22Context k)).map _ = _
    rw [hgood]
    rfl
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact hzero _ (by simp)
      · exact hcuts _ (by simp)
      · exact hcuts _ (by simp)
      · exact hcuts _ (by simp)
    · exact hholds b hb
