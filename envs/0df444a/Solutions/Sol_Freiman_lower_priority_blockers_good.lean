-- Prove2me | solution 1 for Freiman.lower_priority_blockers_good
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-09-16T00:22:05.410767+00:00
-- url     : https://prove2.me/submissions/1cf12481-dd73-4379-994e-126129e6ee75

import Theorems.Thm_Freiman_trunk_active_geometry
import Theorems.Thm_Freiman_lower_early_geometry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Freiman

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

-- Exact dictionary between the source certificate thresholds and A3, A9, A16.
private lemma blocker_thresholds (p : LowerPair) :
    certThresholdVal lowerHistoryH7.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (31/100) 3 63 25 66 ∧
    certThresholdVal lowerHistoryH9.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 ∧
    certThresholdVal trunkH18.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (183/250) 25 36 30 63 := by
  classical
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h1 : (1:ℝ) < Real.sqrt 3 := by nlinarith
  have h2 : Real.sqrt 3 < (2:ℝ) := by nlinarith
  have e0 : (3:ℝ) + (Real.sqrt 3 - 1) = 2 + Real.sqrt 3 := by ring
  have e1 : (1:ℝ) / (2 + Real.sqrt 3) = 2 - Real.sqrt 3 := by
    rw [div_eq_iff (by nlinarith)]; nlinarith
  have t3 : lowerTheta 3 = 2 - Real.sqrt 3 := by
    show prefixEval [3] lowerTau = _
    simp only [prefixEval, lowerTau]; push_cast; rw [e0, e1]
  have t25 : lowerTheta 25 = (5 + Real.sqrt 3) / 22 := by
    show prefixEval [3,3] lowerTau = _
    simp only [prefixEval, lowerTau]; push_cast
    rw [e0, e1, show (3:ℝ) + (2 - Real.sqrt 3) = 5 - Real.sqrt 3 by ring,
      div_eq_iff (by nlinarith)]
    nlinarith
  have t63 : lowerTheta 63 = (4 + Real.sqrt 3) / 13 := by
    show prefixEval [2,3] lowerTau = _
    simp only [prefixEval, lowerTau]; push_cast
    rw [e0, e1, show (2:ℝ) + (2 - Real.sqrt 3) = 4 - Real.sqrt 3 by ring,
      div_eq_iff (by nlinarith)]
    nlinarith
  have t66 : lowerTheta 66 = (9 - Real.sqrt 3) / 13 := by
    show prefixEval [1,1,3] lowerTau = _
    simp only [prefixEval, lowerTau]; push_cast
    rw [e0, e1, show (1:ℝ) + (2 - Real.sqrt 3) = 3 - Real.sqrt 3 by ring,
      show (1:ℝ) / (3 - Real.sqrt 3) = (3 + Real.sqrt 3) / 6 by
        rw [div_eq_div_iff (by nlinarith) (by norm_num)]; nlinarith,
      show (1:ℝ) + (3 + Real.sqrt 3) / 6 = (9 + Real.sqrt 3) / 6 by ring,
      div_div_eq_mul_div, one_mul, div_eq_div_iff (by nlinarith) (by norm_num)]
    nlinarith
  have t36 : lowerTheta 36 = (Real.sqrt 3 - 1) / 2 := by
    show prefixEval [] (lowerTau / 2) = _
    simp only [prefixEval, lowerTau]
  have cfl : ∀ q : ℚ, certFieldVal (lowerHistoryRat q) = (q : ℝ) := by
    intro q; simp [certFieldVal, lowerHistoryRat]
  have hT3 : lowerHistoryTheta 3 = (⟨2,-1,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
      lowerHistoryInv, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
      lowerHistoryTau, CertField.mk.injEq]
  have hT25 : lowerHistoryTheta 25 = (⟨5/22,1/22,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
      lowerHistoryInv, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
      lowerHistoryTau, CertField.mk.injEq]
  have hT63 : lowerHistoryTheta 63 = (⟨4/13,1/13,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
      lowerHistoryInv, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
      lowerHistoryTau, CertField.mk.injEq]
  have hT66 : lowerHistoryTheta 66 = (⟨9/13,-1/13,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
      lowerHistoryInv, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
      lowerHistoryTau, CertField.mk.injEq]
  have hT36 : lowerHistoryTheta 36 = (⟨-1/2,1/2,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, certFieldScale, lowerHistoryTau, CertField.mk.injEq]
  have v3 : certFieldVal (lowerHistoryTheta 3) = lowerTheta 3 := by
    rw [hT3, t3]; simp [certFieldVal]; push_cast; ring
  have v25 : certFieldVal (lowerHistoryTheta 25) = lowerTheta 25 := by
    rw [hT25, t25]; simp [certFieldVal]; push_cast; ring
  have v63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63 := by
    rw [hT63, t63]; simp [certFieldVal]; push_cast; ring
  have v66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66 := by
    rw [hT66, t66]; simp [certFieldVal]; push_cast; ring
  have v36 : certFieldVal (lowerHistoryTheta 36) = lowerTheta 36 := by
    rw [hT36, t36]; simp [certFieldVal]; push_cast; ring
  have thr : ∀ (c a b u v : CertField) (r s : ℝ),
      certThresholdVal (lowerHistoryThreshold c (a,b) (u,v)) r s
        = certFieldVal c * ((1+s*certFieldVal u) * (1+s*certFieldVal v))
          / ((1+r*certFieldVal a) * (1+r*certFieldVal b)) := by
    intro c a b u v r s
    simp only [lowerHistoryThreshold, lowerHistorySort, certThresholdVal, certThresholdNum,
      certThresholdDen]
    split_ifs <;> ring
  have t30 : lowerTheta 30 = (15 - Real.sqrt 3) / 37 := by
    show prefixEval [2,1,3] lowerTau = _
    simp only [prefixEval, lowerTau]; push_cast
    rw [e0, e1, show (1:ℝ) + (2 - Real.sqrt 3) = 3 - Real.sqrt 3 by ring,
      show (1:ℝ) / (3 - Real.sqrt 3) = (3 + Real.sqrt 3) / 6 by
        rw [div_eq_div_iff (by nlinarith) (by norm_num)]; nlinarith,
      show (2:ℝ) + (3 + Real.sqrt 3) / 6 = (15 + Real.sqrt 3) / 6 by ring,
      div_div_eq_mul_div, one_mul, div_eq_div_iff (by nlinarith) (by norm_num)]
    nlinarith
  have hT30 : lowerHistoryCF [2,1,3] lowerHistoryTau = (⟨15/37,-1/37,0,0⟩ : CertField) := by
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
      lowerHistoryInv, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
      lowerHistoryTau, CertField.mk.injEq]
  have v30 : certFieldVal (lowerHistoryCF [2,1,3] lowerHistoryTau) = lowerTheta 30 := by
    rw [hT30, t30]; simp [certFieldVal]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · change certThresholdVal (lowerHistoryThreshold (lowerHistoryRat (31/100))
      (lowerHistoryTheta 3, lowerHistoryTheta 25)
      (lowerHistoryTheta 63, lowerHistoryTheta 66)) _ _ = _
    rw [thr, cfl, v3, v25, v63, v66]
    simp only [lowerThreshold]; push_cast; ring
  · change certThresholdVal (lowerHistoryThreshold (⟨3/2,-1/2,0,0⟩ : CertField)
      (lowerHistoryTheta 36, lowerHistoryTheta 63)
      (lowerHistoryTheta 63, lowerHistoryTheta 66)) _ _ = _
    rw [thr, v36, v63, v66]
    simp only [lowerThreshold, certFieldVal]; push_cast; ring
  · change certThresholdVal (lowerHistoryThreshold (lowerHistoryRat (183/250))
      (lowerHistoryTheta 25, lowerHistoryCF [2,1,3] lowerHistoryTau)
      (lowerHistoryTheta 36, lowerHistoryTheta 63)) _ _ = _
    rw [thr, cfl, v25, v30, v36, v63]
    simp only [lowerThreshold]; push_cast; ring

private lemma blocker_complement (b : CertBound) (r s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q := by
  cases b with
  | mk lo st th => cases lo <;> cases st <;>
      simp [certBoundHolds, lowerHistoryComplement, not_lt, not_le]

private lemma blocker_strict_good (p : LowerPair) (hp : lowerStrictGood p) :
    lowerGood p := by
  exact ⟨max (lowerEndpoint (lowerChild p ([1],[])) false)
      (lowerEndpoint (lowerChild p ([2],[])) false),
    ⟨le_max_left _ _, le_of_lt (lt_of_lt_of_le hp (min_le_left _ _))⟩,
    ⟨le_max_right _ _, le_of_lt (lt_of_lt_of_le hp (min_le_right _ _))⟩⟩

-- Select an actual source row containing C32, regardless of the A20/periodic split.
private lemma blocker_large_plan (C : LowerHistoryContext) (r s q : ℝ)
    (hl : ¬ ([3,1] : List ℕ+).IsSuffix C.words.1)
    (h7 : certBoundHolds lowerHistoryH7 r s q)
    (h9 : certBoundHolds (lowerHistoryComplement lowerHistoryH9) r s q) :
    ∃ i : ℕ, i < (trunkSourcePlans C).length ∧
      trunkHolds ((trunkSourcePlans C)[i]?.getD ⟨[],[],[]⟩).cuts r s q ∧
      (([3],[2]) : LowerLabel) ∈ ((trunkSourcePlans C)[i]?.getD ⟨[],[],[]⟩).labels := by
  classical
  by_cases hr : ([3,1] : List ℕ+).IsSuffix C.words.2 <;>
    by_cases h20 : certBoundHolds trunkH20 r s q <;>
    by_cases hsh : certBoundHolds trunkShorten r s q
  all_goals
    first
    | (refine ⟨3, ?_, ?_, ?_⟩ <;>
        simp_all [trunkSourcePlans, trunkHolds, blocker_complement] <;> done)
    | (refine ⟨4, ?_, ?_, ?_⟩ <;>
        simp_all [trunkSourcePlans, trunkHolds, blocker_complement] <;> done)
    | (refine ⟨5, ?_, ?_, ?_⟩ <;>
        simp_all [trunkSourcePlans, trunkHolds, blocker_complement] <;> done)
    | (refine ⟨6, ?_, ?_, ?_⟩ <;>
        simp_all [trunkSourcePlans, trunkHolds, blocker_complement] <;> done)

private lemma blocker_early_plan (C : LowerHistoryContext) (r s q : ℝ)
    (hl : ¬ ([3,1] : List ℕ+).IsSuffix C.words.1)
    (hr : ([3,1] : List ℕ+).IsSuffix C.words.2)
    (h7 : certBoundHolds lowerHistoryH7 r s q)
    (h9 : certBoundHolds lowerHistoryH9 r s q)
    (h18 : certBoundHolds trunkH18 r s q) :
    ∃ i : ℕ, i < (trunkSourcePlans C).length ∧
      trunkHolds ((trunkSourcePlans C)[i]?.getD ⟨[],[],[]⟩).cuts r s q ∧
      (([2],[2]) : LowerLabel) ∈ ((trunkSourcePlans C)[i]?.getD ⟨[],[],[]⟩).labels := by
  classical
  refine ⟨2, ?_, ?_, ?_⟩ <;>
    simp_all [trunkSourcePlans, trunkHolds]

-- Only the current state is needed; the history supplies that state at depth n.
private lemma blocker_state_good (t : ℝ) (p : LowerPair) (hs : lowerState t p) :
    lowerPreferredGood p := by
  classical
  obtain ⟨e7, e9, e18⟩ := blocker_thresholds p
  have h7 : ¬ lowerA p 3 → certBoundHolds lowerHistoryH7
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) := by
    intro h
    change certThresholdVal lowerHistoryH7.threshold _ _ ≤ _
    rw [e7]
    exact not_lt.mp h
  have h9 : certBoundHolds lowerHistoryH9
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) ↔ lowerA p 9 := by
    change (_ ≤ certThresholdVal lowerHistoryH9.threshold _ _) ↔ _
    rw [e9]
    rfl
  have h18 : ¬ lowerA p 16 → certBoundHolds trunkH18
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) := by
    intro h
    change _ ≤ certThresholdVal trunkH18.threshold _ _
    rw [e18]
    exact not_lt.mp h
  constructor
  · rintro ⟨hm, ha3, ha9, hl, hoff⟩
    have hls : ¬ lowerLStar p := by
      intro hstar
      apply hl
      exact List.IsSuffix.trans (by decide : ([3,1] : List ℕ+).IsSuffix [3,1,3,1]) hstar
    have hrs : ¬ lowerRStar p := by
      intro hr
      rcases hoff with hoff | ⟨_, k, hk, heq⟩
      · by_cases h20 : lowerA p 20 <;>
          simp [lowerEqualList, hm, ha3, ha9, hl, hls, hr, h20] at hoff
      · have heq' := congrArg (fun l : LowerLabel => l.1 = l.2) heq
        simp at heq'
    refine ⟨Or.inl ?_, ?_⟩
    · simp [lowerEqualList, hm, ha3, ha9, hl, hls, hrs]
    · obtain ⟨k, hf, _, hg⟩ := trunk_active_geometry t p hs hm
      have hlf : ¬ ([3,1] : List ℕ+).IsSuffix (trunkCatalog.states k).context.words.1 :=
        fun h => hl (hf.1.2.2.mpr h)
      obtain ⟨i, hi, hcuts, hmem⟩ := blocker_large_plan (trunkCatalog.states k).context
        _ _ _ hlf (h7 ha3) ((blocker_complement _ _ _ _).mpr (fun h => ha9 (h9.mp h)))
      exact blocker_strict_good _ ((hg i hi hcuts).strictGood _ hmem)
  · rintro ⟨hm, ha3, ha9, hl, hr, ha16, _⟩
    have hbranch : ¬ (¬ lowerR p ∨ lowerA p 16) := by simp [hr, ha16]
    constructor
    · intro hrs
      refine ⟨Or.inl ?_, ?_⟩
      · simp [lowerEqualList, hm, ha3, ha9, hl, hbranch, hrs]
      · obtain ⟨k, hf, _, hg⟩ := trunk_active_geometry t p hs hm
        have hlf : ¬ ([3,1] : List ℕ+).IsSuffix (trunkCatalog.states k).context.words.1 :=
          fun h => hl (hf.1.2.2.mpr h)
        have hrf : ([3,1] : List ℕ+).IsSuffix (trunkCatalog.states k).context.words.2 :=
          hf.2.1.2.2.mp hr
        obtain ⟨i, hi, hcuts, hmem⟩ := blocker_early_plan (trunkCatalog.states k).context
          _ _ _ hlf hrf (h7 ha3) (h9.mpr ha9) (h18 ha16)
        exact blocker_strict_good _ ((hg i hi hcuts).strictGood _ hmem)
    · intro hrs l hmem
      refine ⟨Or.inl ?_, ?_⟩
      · simpa [lowerEqualList, hm, ha3, ha9, hl, hbranch, hrs] using
          (Or.inr (Or.inl hmem) : l = ([1],[]) ∨ l ∈ lowerEarlyList p ∨ l = ([2],[]))
      · exact (lower_early_geometry t p hs ⟨hm, ha3, ha9, hl, hr, ha16, hrs⟩).1 l hmem

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) : lowerPreferredGood (h n) := by
  exact blocker_state_good t (h n) (hh.2.1 n le_rfl)
