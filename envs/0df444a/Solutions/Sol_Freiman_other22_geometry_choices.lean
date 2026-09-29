-- Prove2me | solution 1 for Freiman.other22_geometry_choices
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-15T20:04:24.121969+00:00
-- url     : https://prove2.me/submissions/b7c609d9-8062-4de5-b779-b9a9e10102c8

import Definitions.Def_Freiman_other22Verification
import Theorems.Thm_Freiman_lowerHistory_pull_value
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

private theorem choices_at_birth (Z B : LowerPair) (hn : lowerNormalize B = B)
    (he : B = (Z.1 ++ [2], Z.2 ++ [3]))
    (hs : lowerA B 3 ∨ (¬ lowerA B 3 ∧ lowerA B 9)) :
    ∃ bs ∈ [[lowerHistoryComplement lowerHistoryH7], [lowerHistoryH7,lowerHistoryH9]],
      lowerHistoryAtBase Z (bs.map fun b => lowerHistoryPull b ([2],[3]) false) := by
  have ht := source_tests B hn
  have transfer (b : CertBound)
      (hb : b = lowerHistoryComplement lowerHistoryH7 ∨ b = lowerHistoryH7 ∨ b = lowerHistoryH9)
      (h : lowerHistoryAtBase B [b]) :
      lowerHistoryAtBase Z [lowerHistoryPull b ([2],[3]) false] := by
    rcases bound_positive b hb with ⟨hc,hx0,hx1,hy0,hy1⟩
    apply (lowerHistory_pull_value Z ([2],[3]) b false hc hx0 hx1 hy0 hy1).mp
    simpa [lowerHistoryOrient, lowerHistoryAppend, he] using h
  rcases hs with h | ⟨h,h'⟩
  · refine ⟨[lowerHistoryComplement lowerHistoryH7], by simp, ?_⟩
    exact transfer _ (Or.inl rfl) (ht.1.mpr h)
  · refine ⟨[lowerHistoryH7,lowerHistoryH9], by simp, ?_⟩
    have h1 := transfer _ (Or.inr (Or.inl rfl)) (ht.2.1.mpr h)
    have h2 := transfer _ (Or.inr (Or.inr rfl)) (ht.2.2.mpr h')
    simpa [lowerHistoryAtBase, lowerHistoryConditions] using And.intro h1 h2

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryChoiceEvents Z (other22Paths k) := by
  have he : B = (Z.1 ++ [2], Z.2 ++ [3]) := by
    rw [h.birth]
    simp [lowerChild, h.normalizedZ]
  have hbirth := choices_at_birth Z B h.normalizedB he h.sourceB
  have hsteps : (other22Paths k).steps = [(([2],[]),true),(([1],[]),false)] := by
    fin_cases k <;> rfl
  intro j l r hj
  have hjlt : j < 2 := by
    have hh := List.getElem?_eq_some_iff.mp hj
    simpa [hsteps] using hh.1
  interval_cases j
  · have heq : l = ([2],[]) ∧ r = true := by simpa [hsteps, eq_comm] using hj
    rcases heq with ⟨rfl,rfl⟩
    fin_cases k <;> exact hbirth
  · have heq : l = ([1],[]) ∧ r = false := by simpa [hsteps, eq_comm] using hj
    rcases heq with ⟨rfl,rfl⟩
    refine ⟨[], ?_, ?_⟩
    · simp [lowerHistorySourceChoices]
    · simp [lowerHistoryAtBase, lowerHistoryConditions]
