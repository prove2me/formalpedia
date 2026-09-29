-- Prove2me | solution 1 for Freiman.late_base_from_theta_width
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T19:32:51.500484+00:00
-- url     : https://prove2.me/submissions/20d5acf4-ace0-440e-85de-24f6a0298850

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

open Freiman

theorem solution (ht : ∀ i ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ), certFieldVal (lowerHistoryTheta i) = lowerTheta i) (hw : LowerHistoryWidthLaw) (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) :
    lateHolds lateRootBounds (lateR p) (lateS p) (lateQ p) := by
  classical
  -- basic facts about √3
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h1 : (1:ℝ) < Real.sqrt 3 := by nlinarith
  have h2 : Real.sqrt 3 < (2:ℝ) := by nlinarith
  -- exact values of the five lowerTheta constants that occur in the three root bounds
  have e0 : (3:ℝ) + (Real.sqrt 3 - 1) = 2 + Real.sqrt 3 := by ring
  have e1 : (1:ℝ) / (2 + Real.sqrt 3) = 2 - Real.sqrt 3 := by
    rw [div_eq_iff (by nlinarith)]; nlinarith
  have t3 : lowerTheta 3 = 2 - Real.sqrt 3 := by
    show prefixEval [3] lowerTau = _
    simp only [prefixEval, lowerTau]
    push_cast
    rw [e0, e1]
  have t25 : lowerTheta 25 = (5 + Real.sqrt 3) / 22 := by
    show prefixEval [3,3] lowerTau = _
    simp only [prefixEval, lowerTau]
    push_cast
    rw [e0, e1, show (3:ℝ) + (2 - Real.sqrt 3) = 5 - Real.sqrt 3 by ring,
      div_eq_iff (by nlinarith)]
    nlinarith
  have t63 : lowerTheta 63 = (4 + Real.sqrt 3) / 13 := by
    show prefixEval [2,3] lowerTau = _
    simp only [prefixEval, lowerTau]
    push_cast
    rw [e0, e1, show (2:ℝ) + (2 - Real.sqrt 3) = 4 - Real.sqrt 3 by ring,
      div_eq_iff (by nlinarith)]
    nlinarith
  have t66 : lowerTheta 66 = (9 - Real.sqrt 3) / 13 := by
    show prefixEval [1,1,3] lowerTau = _
    simp only [prefixEval, lowerTau]
    push_cast
    rw [e0, e1, show (1:ℝ) + (2 - Real.sqrt 3) = 3 - Real.sqrt 3 by ring,
      show (1:ℝ) / (3 - Real.sqrt 3) = (3 + Real.sqrt 3) / 6 by
        rw [div_eq_div_iff (by nlinarith) (by norm_num)]; nlinarith,
      show (1:ℝ) + (3 + Real.sqrt 3) / 6 = (9 + Real.sqrt 3) / 6 by ring,
      div_div_eq_mul_div, one_mul, div_eq_div_iff (by nlinarith) (by norm_num)]
    nlinarith
  have t36 : lowerTheta 36 = (Real.sqrt 3 - 1) / 2 := by
    show prefixEval [] (lowerTau / 2) = _
    simp only [prefixEval, lowerTau]
  -- the width-threshold of the empty word pair
  have hWH : lowerHistoryWH (([],[]) : LowerPair) =
      ⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩ := by
    norm_num [lowerHistoryWH, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex,
      lowerHistoryAbs, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign,
      lowerHistoryDiv, lowerHistoryInv, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryRat,
      certFieldMul, certFieldSub, certFieldAdd, certFieldScale,
      lowerHistoryAlpha, lowerHistoryBeta, CertThreshold.mk.injEq, CertField.mk.injEq]
  have hroot : lateRootBounds =
      [(⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,
          ⟨(9/13),(-1/13),0,0⟩⟩⟩ : CertBound),
       (⟨true,false,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,
          ⟨(9/13),(-1/13),0,0⟩⟩⟩ : CertBound),
       (⟨false,false,lowerHistoryWH (([],[]) : LowerPair)⟩ : CertBound)] := by
    rw [hWH]; rfl
  -- the two selection hypotheses, as real inequalities
  have hA3 : lowerThreshold p (31/100) 3 63 25 66 ≤ lowerScale (lowerNormalize p) :=
    not_lt.mp hd.2.1
  have hA9 : lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 < lowerScale (lowerNormalize p) :=
    not_le.mp hd.2.2.1
  -- the normalized pair has its wide side first
  have hnorm : lowerWidth ((lowerNormalize p).2 ++ ([] : List ℕ+)) ≤
      lowerWidth ((lowerNormalize p).1 ++ ([] : List ℕ+)) := by
    simp only [List.append_nil]
    unfold lowerNormalize
    by_cases hwd : lowerWidth p.2 ≤ lowerWidth p.1
    · simp only [hwd, if_true] <;> exact hwd
    · simp only [hwd, if_false] <;> exact le_of_lt (not_le.mp hwd)
  intro b hb
  rw [hroot] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · show certThresholdVal
      (⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,
        ⟨(9/13),(-1/13),0,0⟩⟩ : CertThreshold) (lateR p) (lateS p) ≤ lateQ p
    have key : certThresholdVal
        (⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,
          ⟨(9/13),(-1/13),0,0⟩⟩ : CertThreshold) (lateR p) (lateS p)
        = lowerThreshold p (31/100) 3 63 25 66 := by
      simp only [certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal,
        lowerThreshold, lateR, lateS]
      rw [t3, t25, t63, t66]
      push_cast
      congr 1 <;> ring
    rw [key]
    exact hA3
  · show certThresholdVal
      (⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,
        ⟨(9/13),(-1/13),0,0⟩⟩ : CertThreshold) (lateR p) (lateS p) ≤ lateQ p
    have key : certThresholdVal
        (⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,
          ⟨(9/13),(-1/13),0,0⟩⟩ : CertThreshold) (lateR p) (lateS p)
        = lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 := by
      simp only [certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal,
        lowerThreshold, lateR, lateS]
      rw [t36, t63, t66]
      push_cast
      congr 1 <;> ring
    rw [key]
    exact le_of_lt hA9
  · exact (hw (lowerNormalize p) ([],[])).1.mp hnorm _ (List.mem_singleton_self _)
