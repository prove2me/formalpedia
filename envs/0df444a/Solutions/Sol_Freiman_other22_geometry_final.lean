-- Prove2me | solution 1 for Freiman.other22_geometry_final
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-15T20:13:27.011203+00:00
-- url     : https://prove2.me/submissions/7e6333cb-a16f-4ca1-8bc0-6afcdadf6e71

import Definitions.Def_Freiman_other22Verification
import Theorems.Thm_Freiman_lowerHistory_pull_value
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

private theorem bound_positive (b : CertBound)
    (hb : b = lowerHistoryComplement lowerHistoryH7 ∨ b = lowerHistoryH7 ∨ b = lowerHistoryH9) :
    0 < certFieldVal b.threshold.c ∧
    0 ≤ certFieldVal b.threshold.x0 ∧ 0 ≤ certFieldVal b.threshold.x1 ∧
    0 ≤ certFieldVal b.threshold.y0 ∧ 0 ≤ certFieldVal b.threshold.y1 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hl : (1:ℝ) < Real.sqrt 3 := by nlinarith
  have hu : Real.sqrt 3 < (2:ℝ) := by nlinarith
  rcases hb with rfl | rfl | rfl
  all_goals norm_num [lowerHistoryComplement, lowerHistoryH7, lowerHistoryH9,
    lowerHistoryPB, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex,
    lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryTau, certFieldVal,
    certFieldAdd, certFieldScale, certFieldMul]
  all_goals repeat' constructor
  all_goals nlinarith

private theorem normal_bound_positive :
    0 < certFieldVal lowerHistoryHN.threshold.c ∧
    0 ≤ certFieldVal lowerHistoryHN.threshold.x0 ∧
    0 ≤ certFieldVal lowerHistoryHN.threshold.x1 ∧
    0 ≤ certFieldVal lowerHistoryHN.threshold.y0 ∧
    0 ≤ certFieldVal lowerHistoryHN.threshold.y1 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21:ℝ)
  have hl : (4:ℝ) < Real.sqrt 21 := by nlinarith
  norm_num [lowerHistoryHN, lowerHistoryWH, lowerHistoryThreshold,
    lowerHistorySort, lowerHistoryLex, lowerHistoryCF, lowerHistoryMatrix,
    lowerHistoryDiv, lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha,
    lowerHistoryBeta, lowerHistoryAbs, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg,
    certFieldVal, certFieldSub, certFieldAdd, certFieldScale, certFieldMul]
  all_goals repeat' constructor
  all_goals nlinarith

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

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryFinalEvent Z (other22Paths k) := by
  have hB : B = (Z.1 ++ [2], Z.2 ++ [3]) := by
    rw [h.birth]
    simp [lowerChild, h.normalizedZ]
  have hS : S = (Z.2 ++ [3,1], Z.1 ++ [2,2]) := by
    rw [h.stepS]
    simp [lowerChild, h.normalizedR, hB, List.append_assoc]
  have hs := final_bounds S h.normalizedS h.largeS3 h.largeS9
  have hpull : lowerHistoryAtBase Z
      ([lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,lowerHistoryHN].map
        fun b => lowerHistoryPull b ([2,2],[3,1]) true) := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    have hpos : 0 < certFieldVal a.threshold.c ∧
        0 ≤ certFieldVal a.threshold.x0 ∧ 0 ≤ certFieldVal a.threshold.x1 ∧
        0 ≤ certFieldVal a.threshold.y0 ∧ 0 ≤ certFieldVal a.threshold.y1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact bound_positive _ (Or.inr (Or.inl rfl))
      · exact bound_positive lowerHistoryH9 (Or.inr (Or.inr rfl))
      · exact normal_bound_positive
    have hat : lowerHistoryAtBase S [a] := by
      intro b hb
      have he : b = a := List.mem_singleton.mp hb
      subst b
      exact hs a ha
    have ht := (lowerHistory_pull_value Z ([2,2],[3,1]) a true
      hpos.1 hpos.2.1 hpos.2.2.1 hpos.2.2.2.1 hpos.2.2.2.2).mp
      (by simpa [lowerHistoryOrient, lowerHistoryAppend, hS] using hat)
    exact ht _ (by simp)
  fin_cases k <;> exact hpull
