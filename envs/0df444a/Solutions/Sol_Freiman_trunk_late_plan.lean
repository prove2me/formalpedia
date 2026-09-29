-- Prove2me | solution 1 for Freiman.trunk_late_plan
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T19:34:38.56724+00:00
-- url     : https://prove2.me/submissions/579524e8-da13-4b84-accb-55aeb28e7362

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) (k : Fin 16)
    (hf : lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context) :
    ∃ pi : ℕ, pi < (trunkSourcePlans (trunkCatalog.states k).context).length ∧
    trunkHolds (trunkPlanAt (trunkCatalog.states k) pi).cuts (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) ∧
    ([2],[2]) ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels ∧ ([2],[1]) ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels := by
  classical
  -- √3 arithmetic
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
  -- exact CertField literals of the five history constants
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
  -- the threshold value of a sorted pair-threshold
  have thr : ∀ (c a b u v : CertField) (r s : ℝ),
      certThresholdVal (lowerHistoryThreshold c (a,b) (u,v)) r s
        = certFieldVal c * ((1+s*certFieldVal u) * (1+s*certFieldVal v))
          / ((1+r*certFieldVal a) * (1+r*certFieldVal b)) := by
    intro c a b u v r s
    simp only [lowerHistoryThreshold, lowerHistorySort, certThresholdVal, certThresholdNum,
      certThresholdDen]
    split_ifs <;> ring
  -- the two selection facts
  have hA3 : lowerThreshold p (31/100) 3 63 25 66 ≤ lowerScale (lowerNormalize p) :=
    not_lt.mp hd.2.1
  have hA9 : lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 < lowerScale (lowerNormalize p) :=
    not_le.mp hd.2.2.1
  -- the context is a left-marked one, so the third source plan is the "large" plan
  have hL : ([3,1] : List ℕ+).IsSuffix (trunkCatalog.states k).context.words.1 :=
    hf.1.2.2.mp hd.2.2.2.1
  have hplans : trunkSourcePlans (trunkCatalog.states k).context =
      [⟨[lowerHistoryComplement lowerHistoryH7], [([1],[]),([2],[])], []⟩,
       ⟨[lowerHistoryH7,lowerHistoryH9], [([1],[]),([2],[])], []⟩,
       ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9],
        [([1],[]),([2],[1]),([2],[2]),([2],[3])],
        [((([2],[1]) : LowerLabel),(([2],[2]) : LowerLabel))]⟩] := by
    simp [trunkSourcePlans, hL]
  have hpa : trunkPlanAt (trunkCatalog.states k) 2 =
      ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9],
       [([1],[]),([2],[1]),([2],[2]),([2],[3])],
       [((([2],[1]) : LowerLabel),(([2],[2]) : LowerLabel))]⟩ := by
    simp [trunkPlanAt, hplans]
  refine ⟨2, ?_, ?_, ?_, ?_⟩
  · rw [hplans]; norm_num
  · rw [hpa]
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · show certThresholdVal (lowerHistoryThreshold (lowerHistoryRat (31/100))
        (lowerHistoryTheta 3, lowerHistoryTheta 25) (lowerHistoryTheta 63, lowerHistoryTheta 66))
        (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
        ≤ lowerScale (lowerNormalize p)
      rw [thr, cfl, v3, v25, v63, v66]
      refine le_trans (le_of_eq ?_) hA3
      simp only [lowerThreshold]
      push_cast
      ring
    · show certThresholdVal (lowerHistoryThreshold (⟨3/2,-1/2,0,0⟩ : CertField)
        (lowerHistoryTheta 36, lowerHistoryTheta 63) (lowerHistoryTheta 63, lowerHistoryTheta 66))
        (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
        < lowerScale (lowerNormalize p)
      rw [thr, v36, v63, v66]
      refine lt_of_le_of_lt (le_of_eq ?_) hA9
      simp only [lowerThreshold, certFieldVal]
      push_cast
      ring
  · rw [hpa]; simp
  · rw [hpa]; simp
