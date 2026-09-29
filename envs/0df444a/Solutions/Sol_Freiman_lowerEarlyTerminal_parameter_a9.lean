-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_parameter_a9
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:00:11.643798+00:00
-- url     : https://prove2.me/submissions/9712552c-5024-4786-9078-599acb40a479

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open Freiman

theorem hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
theorem hs21 : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
theorem sq3lo : (1732050807/1000000000:ℝ) < Real.sqrt 3 := by
  nlinarith [hs3, Real.sqrt_nonneg 3]
theorem sq3hi : Real.sqrt 3 < (1732050809/1000000000:ℝ) := by
  nlinarith [hs3, Real.sqrt_nonneg 3]
theorem s21lo : (4582575694/1000000000:ℝ) < Real.sqrt 21 := by
  nlinarith [hs21, Real.sqrt_nonneg 21]
theorem s21hi : Real.sqrt 21 < (4582575696/1000000000:ℝ) := by
  nlinarith [hs21, Real.sqrt_nonneg 21]

theorem pe_step (n : ℕ+) (w : List ℕ+) (x ρ A B A' B' r : ℝ)
    (hn : ((n:ℕ):ℝ) = r)
    (hw : prefixEval w x = A' + B' * ρ)
    (hpos : (0:ℝ) < r + (A' + B' * ρ))
    (hid : (A + B * ρ) * (r + (A' + B' * ρ)) = 1) :
    prefixEval (n :: w) x = A + B * ρ := by
  have h1 : prefixEval (n :: w) x = 1 / (((n : ℕ) : ℝ) + prefixEval w x) := rfl
  rw [h1, hn, hw, div_eq_iff (ne_of_gt hpos)]
  exact hid.symm

theorem v_t_e : prefixEval ([]:List ℕ+) lowerTau = (-1:ℝ) + (1:ℝ) * (Real.sqrt 3) := by
  simp only [prefixEval, lowerTau]; ring
theorem v_t_3 : prefixEval ([3]:List ℕ+) lowerTau = (2:ℝ) + (-1:ℝ) * (Real.sqrt 3) :=
  pe_step 3 [] lowerTau (Real.sqrt 3) (2:ℝ) (-1:ℝ) (-1:ℝ) (1:ℝ) (3:ℝ) (by norm_num) v_t_e (by linarith [sq3lo, sq3hi])
    (by linear_combination ((-1:ℝ)) * hs3)
theorem th3 : lowerTheta 3 = (2:ℝ) + (-1:ℝ) * (Real.sqrt 3) := by
  have h : lowerTheta 3 = prefixEval ([3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_3]
theorem v_a_e : prefixEval ([]:List ℕ+) lowerAlpha = ((-1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 21) := by
  simp only [prefixEval, lowerAlpha]; ring
theorem v_a_2 : prefixEval ([2]:List ℕ+) lowerAlpha = ((9:ℝ)/10) + ((-1:ℝ)/10) * (Real.sqrt 21) :=
  pe_step 2 [] lowerAlpha (Real.sqrt 21) ((9:ℝ)/10) ((-1:ℝ)/10) ((-1:ℝ)/2) ((1:ℝ)/6) (2:ℝ) (by norm_num) v_a_e (by linarith [s21lo, s21hi])
    (by linear_combination (((-1:ℝ)/60)) * hs21)
theorem v_a_12 : prefixEval ([1, 2]:List ℕ+) lowerAlpha = ((19:ℝ)/34) + ((1:ℝ)/34) * (Real.sqrt 21) :=
  pe_step 1 [2] lowerAlpha (Real.sqrt 21) ((19:ℝ)/34) ((1:ℝ)/34) ((9:ℝ)/10) ((-1:ℝ)/10) (1:ℝ) (by norm_num) v_a_2 (by linarith [s21lo, s21hi])
    (by linear_combination (((-1:ℝ)/340)) * hs21)
theorem v_a_312 : prefixEval ([3, 1, 2]:List ℕ+) lowerAlpha = ((121:ℝ)/430) + ((-1:ℝ)/430) * (Real.sqrt 21) :=
  pe_step 3 [1, 2] lowerAlpha (Real.sqrt 21) ((121:ℝ)/430) ((-1:ℝ)/430) ((19:ℝ)/34) ((1:ℝ)/34) (3:ℝ) (by norm_num) v_a_12 (by linarith [s21lo, s21hi])
    (by linear_combination (((-1:ℝ)/14620)) * hs21)
theorem th6 : lowerTheta 6 = ((121:ℝ)/430) + ((-1:ℝ)/430) * (Real.sqrt 21) := by
  have h : lowerTheta 6 = prefixEval ([3, 1, 2]:List ℕ+) lowerAlpha := rfl
  rw [h, v_a_312]
theorem v_t_13 : prefixEval ([1, 3]:List ℕ+) lowerTau = ((1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 3) :=
  pe_step 1 [3] lowerTau (Real.sqrt 3) ((1:ℝ)/2) ((1:ℝ)/6) (2:ℝ) (-1:ℝ) (1:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/6)) * hs3)
theorem v_t_113 : prefixEval ([1, 1, 3]:List ℕ+) lowerTau = ((9:ℝ)/13) + ((-1:ℝ)/13) * (Real.sqrt 3) :=
  pe_step 1 [1, 3] lowerTau (Real.sqrt 3) ((9:ℝ)/13) ((-1:ℝ)/13) ((1:ℝ)/2) ((1:ℝ)/6) (1:ℝ) (by norm_num) v_t_13 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/78)) * hs3)
theorem v_t_1113 : prefixEval ([1, 1, 1, 3]:List ℕ+) lowerTau = ((22:ℝ)/37) + ((1:ℝ)/37) * (Real.sqrt 3) :=
  pe_step 1 [1, 1, 3] lowerTau (Real.sqrt 3) ((22:ℝ)/37) ((1:ℝ)/37) ((9:ℝ)/13) ((-1:ℝ)/13) (1:ℝ) (by norm_num) v_t_113 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/481)) * hs3)
theorem v_t_31113 : prefixEval ([3, 1, 1, 1, 3]:List ℕ+) lowerTau = ((133:ℝ)/478) + ((-1:ℝ)/478) * (Real.sqrt 3) :=
  pe_step 3 [1, 1, 1, 3] lowerTau (Real.sqrt 3) ((133:ℝ)/478) ((-1:ℝ)/478) ((22:ℝ)/37) ((1:ℝ)/37) (3:ℝ) (by norm_num) v_t_1113 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/17686)) * hs3)
theorem th8 : lowerTheta 8 = ((133:ℝ)/478) + ((-1:ℝ)/478) * (Real.sqrt 3) := by
  have h : lowerTheta 8 = prefixEval ([3, 1, 1, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_31113]
theorem v_t_1 : prefixEval ([1]:List ℕ+) lowerTau = (0:ℝ) + ((1:ℝ)/3) * (Real.sqrt 3) :=
  pe_step 1 [] lowerTau (Real.sqrt 3) (0:ℝ) ((1:ℝ)/3) (-1:ℝ) (1:ℝ) (1:ℝ) (by norm_num) v_t_e (by linarith [sq3lo, sq3hi])
    (by linear_combination (((1:ℝ)/3)) * hs3)
theorem v_t_11 : prefixEval ([1, 1]:List ℕ+) lowerTau = ((3:ℝ)/2) + ((-1:ℝ)/2) * (Real.sqrt 3) :=
  pe_step 1 [1] lowerTau (Real.sqrt 3) ((3:ℝ)/2) ((-1:ℝ)/2) (0:ℝ) ((1:ℝ)/3) (1:ℝ) (by norm_num) v_t_1 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/6)) * hs3)
theorem v_t_311 : prefixEval ([3, 1, 1]:List ℕ+) lowerTau = ((3:ℝ)/13) + ((1:ℝ)/39) * (Real.sqrt 3) :=
  pe_step 3 [1, 1] lowerTau (Real.sqrt 3) ((3:ℝ)/13) ((1:ℝ)/39) ((3:ℝ)/2) ((-1:ℝ)/2) (3:ℝ) (by norm_num) v_t_11 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/78)) * hs3)
theorem th10 : lowerTheta 10 = ((3:ℝ)/13) + ((1:ℝ)/39) * (Real.sqrt 3) := by
  have h : lowerTheta 10 = prefixEval ([3, 1, 1]:List ℕ+) lowerTau := rfl
  rw [h, v_t_311]
theorem v_t_3113 : prefixEval ([3, 1, 1, 3]:List ℕ+) lowerTau = ((16:ℝ)/59) + ((1:ℝ)/177) * (Real.sqrt 3) :=
  pe_step 3 [1, 1, 3] lowerTau (Real.sqrt 3) ((16:ℝ)/59) ((1:ℝ)/177) ((9:ℝ)/13) ((-1:ℝ)/13) (3:ℝ) (by norm_num) v_t_113 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/2301)) * hs3)
theorem th13 : lowerTheta 13 = ((16:ℝ)/59) + ((1:ℝ)/177) * (Real.sqrt 3) := by
  have h : lowerTheta 13 = prefixEval ([3, 1, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_3113]
theorem v_h_e : prefixEval ([]:List ℕ+) (lowerTau / 2) = ((-1:ℝ)/2) + ((1:ℝ)/2) * (Real.sqrt 3) := by
  simp only [prefixEval, lowerTau]; ring
theorem v_h_3 : prefixEval ([3]:List ℕ+) (lowerTau / 2) = ((5:ℝ)/11) + ((-1:ℝ)/11) * (Real.sqrt 3) :=
  pe_step 3 [] (lowerTau / 2) (Real.sqrt 3) ((5:ℝ)/11) ((-1:ℝ)/11) ((-1:ℝ)/2) ((1:ℝ)/2) (3:ℝ) (by norm_num) v_h_e (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/22)) * hs3)
theorem th19 : lowerTheta 19 = ((5:ℝ)/11) + ((-1:ℝ)/11) * (Real.sqrt 3) := by
  have h : lowerTheta 19 = prefixEval ([3]:List ℕ+) (lowerTau / 2) := rfl
  rw [h, v_h_3]
theorem v_t_33 : prefixEval ([3, 3]:List ℕ+) lowerTau = ((5:ℝ)/22) + ((1:ℝ)/22) * (Real.sqrt 3) :=
  pe_step 3 [3] lowerTau (Real.sqrt 3) ((5:ℝ)/22) ((1:ℝ)/22) (2:ℝ) (-1:ℝ) (3:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/22)) * hs3)
theorem th25 : lowerTheta 25 = ((5:ℝ)/22) + ((1:ℝ)/22) * (Real.sqrt 3) := by
  have h : lowerTheta 25 = prefixEval ([3, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_33]
theorem v_b_e : prefixEval ([]:List ℕ+) lowerBeta = ((-3:ℝ)/2) + ((1:ℝ)/2) * (Real.sqrt 21) := by
  simp only [prefixEval, lowerBeta]; ring
theorem v_b_2 : prefixEval ([2]:List ℕ+) lowerBeta = ((-1:ℝ)/10) + ((1:ℝ)/10) * (Real.sqrt 21) :=
  pe_step 2 [] lowerBeta (Real.sqrt 21) ((-1:ℝ)/10) ((1:ℝ)/10) ((-3:ℝ)/2) ((1:ℝ)/2) (2:ℝ) (by norm_num) v_b_e (by linarith [s21lo, s21hi])
    (by linear_combination (((1:ℝ)/20)) * hs21)
theorem th29 : lowerTheta 29 = ((-1:ℝ)/10) + ((1:ℝ)/10) * (Real.sqrt 21) := by
  have h : lowerTheta 29 = prefixEval ([2]:List ℕ+) lowerBeta := rfl
  rw [h, v_b_2]
theorem v_t_213 : prefixEval ([2, 1, 3]:List ℕ+) lowerTau = ((15:ℝ)/37) + ((-1:ℝ)/37) * (Real.sqrt 3) :=
  pe_step 2 [1, 3] lowerTau (Real.sqrt 3) ((15:ℝ)/37) ((-1:ℝ)/37) ((1:ℝ)/2) ((1:ℝ)/6) (2:ℝ) (by norm_num) v_t_13 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/222)) * hs3)
theorem th30 : lowerTheta 30 = ((15:ℝ)/37) + ((-1:ℝ)/37) * (Real.sqrt 3) := by
  have h : lowerTheta 30 = prefixEval ([2, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_213]
theorem v_b_12 : prefixEval ([1, 2]:List ℕ+) lowerBeta = ((3:ℝ)/2) + ((-1:ℝ)/6) * (Real.sqrt 21) :=
  pe_step 1 [2] lowerBeta (Real.sqrt 21) ((3:ℝ)/2) ((-1:ℝ)/6) ((-1:ℝ)/10) ((1:ℝ)/10) (1:ℝ) (by norm_num) v_b_2 (by linarith [s21lo, s21hi])
    (by linear_combination (((-1:ℝ)/60)) * hs21)
theorem v_b_212 : prefixEval ([2, 1, 2]:List ℕ+) lowerBeta = ((3:ℝ)/10) + ((1:ℝ)/70) * (Real.sqrt 21) :=
  pe_step 2 [1, 2] lowerBeta (Real.sqrt 21) ((3:ℝ)/10) ((1:ℝ)/70) ((3:ℝ)/2) ((-1:ℝ)/6) (2:ℝ) (by norm_num) v_b_12 (by linarith [s21lo, s21hi])
    (by linear_combination (((-1:ℝ)/420)) * hs21)
theorem th34 : lowerTheta 34 = ((3:ℝ)/10) + ((1:ℝ)/70) * (Real.sqrt 21) := by
  have h : lowerTheta 34 = prefixEval ([2, 1, 2]:List ℕ+) lowerBeta := rfl
  rw [h, v_b_212]
theorem th36 : lowerTheta 36 = ((-1:ℝ)/2) + ((1:ℝ)/2) * (Real.sqrt 3) := by
  have h : lowerTheta 36 = prefixEval ([]:List ℕ+) (lowerTau / 2) := rfl
  rw [h, v_h_e]
theorem v_t_11113 : prefixEval ([1, 1, 1, 1, 3]:List ℕ+) lowerTau = ((59:ℝ)/94) + ((-1:ℝ)/94) * (Real.sqrt 3) :=
  pe_step 1 [1, 1, 1, 3] lowerTau (Real.sqrt 3) ((59:ℝ)/94) ((-1:ℝ)/94) ((22:ℝ)/37) ((1:ℝ)/37) (1:ℝ) (by norm_num) v_t_1113 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/3478)) * hs3)
theorem v_t_211113 : prefixEval ([2, 1, 1, 1, 1, 3]:List ℕ+) lowerTau = ((247:ℝ)/649) + ((1:ℝ)/649) * (Real.sqrt 3) :=
  pe_step 2 [1, 1, 1, 1, 3] lowerTau (Real.sqrt 3) ((247:ℝ)/649) ((1:ℝ)/649) ((59:ℝ)/94) ((-1:ℝ)/94) (2:ℝ) (by norm_num) v_t_11113 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/61006)) * hs3)
theorem th45 : lowerTheta 45 = ((247:ℝ)/649) + ((1:ℝ)/649) * (Real.sqrt 3) := by
  have h : lowerTheta 45 = prefixEval ([2, 1, 1, 1, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_211113]
theorem v_t_23 : prefixEval ([2, 3]:List ℕ+) lowerTau = ((4:ℝ)/13) + ((1:ℝ)/13) * (Real.sqrt 3) :=
  pe_step 2 [3] lowerTau (Real.sqrt 3) ((4:ℝ)/13) ((1:ℝ)/13) (2:ℝ) (-1:ℝ) (2:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/13)) * hs3)
theorem v_t_123 : prefixEval ([1, 2, 3]:List ℕ+) lowerTau = ((17:ℝ)/22) + ((-1:ℝ)/22) * (Real.sqrt 3) :=
  pe_step 1 [2, 3] lowerTau (Real.sqrt 3) ((17:ℝ)/22) ((-1:ℝ)/22) ((4:ℝ)/13) ((1:ℝ)/13) (1:ℝ) (by norm_num) v_t_23 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/286)) * hs3)
theorem v_t_1123 : prefixEval ([1, 1, 2, 3]:List ℕ+) lowerTau = ((13:ℝ)/23) + ((1:ℝ)/69) * (Real.sqrt 3) :=
  pe_step 1 [1, 2, 3] lowerTau (Real.sqrt 3) ((13:ℝ)/23) ((1:ℝ)/69) ((17:ℝ)/22) ((-1:ℝ)/22) (1:ℝ) (by norm_num) v_t_123 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/1518)) * hs3)
theorem v_t_21123 : prefixEval ([2, 1, 1, 2, 3]:List ℕ+) lowerTau = ((177:ℝ)/454) + ((-1:ℝ)/454) * (Real.sqrt 3) :=
  pe_step 2 [1, 1, 2, 3] lowerTau (Real.sqrt 3) ((177:ℝ)/454) ((-1:ℝ)/454) ((13:ℝ)/23) ((1:ℝ)/69) (2:ℝ) (by norm_num) v_t_1123 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/31326)) * hs3)
theorem th47 : lowerTheta 47 = ((177:ℝ)/454) + ((-1:ℝ)/454) * (Real.sqrt 3) := by
  have h : lowerTheta 47 = prefixEval ([2, 1, 1, 2, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_21123]
theorem v_t_2113 : prefixEval ([2, 1, 1, 3]:List ℕ+) lowerTau = ((35:ℝ)/94) + ((1:ℝ)/94) * (Real.sqrt 3) :=
  pe_step 2 [1, 1, 3] lowerTau (Real.sqrt 3) ((35:ℝ)/94) ((1:ℝ)/94) ((9:ℝ)/13) ((-1:ℝ)/13) (2:ℝ) (by norm_num) v_t_113 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/1222)) * hs3)
theorem th54 : lowerTheta 54 = ((35:ℝ)/94) + ((1:ℝ)/94) * (Real.sqrt 3) := by
  have h : lowerTheta 54 = prefixEval ([2, 1, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_2113]
theorem v_t_223 : prefixEval ([2, 2, 3]:List ℕ+) lowerTau = ((10:ℝ)/23) + ((-1:ℝ)/69) * (Real.sqrt 3) :=
  pe_step 2 [2, 3] lowerTau (Real.sqrt 3) ((10:ℝ)/23) ((-1:ℝ)/69) ((4:ℝ)/13) ((1:ℝ)/13) (2:ℝ) (by norm_num) v_t_23 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/897)) * hs3)
theorem th57 : lowerTheta 57 = ((10:ℝ)/23) + ((-1:ℝ)/69) * (Real.sqrt 3) := by
  have h : lowerTheta 57 = prefixEval ([2, 2, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_223]
theorem th63 : lowerTheta 63 = ((4:ℝ)/13) + ((1:ℝ)/13) * (Real.sqrt 3) := by
  have h : lowerTheta 63 = prefixEval ([2, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_23]
theorem th66 : lowerTheta 66 = ((9:ℝ)/13) + ((-1:ℝ)/13) * (Real.sqrt 3) := by
  have h : lowerTheta 66 = prefixEval ([1, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_113]

theorem solution (p : LowerPair) : lowerEarlyTerminalAt p [lowerEarlyTerminalA9] ↔ lowerA p 9 := by
  have hT : certThresholdVal lowerEarlyTerminalA9.threshold (lowerEarlyTerminalR p) (lowerEarlyTerminalS p)
      = lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 := by
    unfold certThresholdVal certThresholdNum certThresholdDen lowerThreshold lowerEarlyTerminalR lowerEarlyTerminalS lowerEarlyTerminalA9
    simp only [certFieldVal]
    rw [th36, th63, th66]
    push_cast
    ring
  have hL : lowerA p 9 ↔ lowerScale (lowerNormalize p) ≤ lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 := by
    simp only [lowerA]
  have h1 : (lowerEarlyTerminalA9 : CertBound).lower = false := rfl
  have h2 : (lowerEarlyTerminalA9 : CertBound).strict = false := rfl
  have h3 : (lowerEarlyTerminalA9 : CertBound).threshold = lowerEarlyTerminalA9.threshold := rfl
  rw [hL]
  unfold lowerEarlyTerminalAt section14Holds
  simp only [List.mem_singleton, forall_eq]
  unfold certBoundHolds
  rw [h3, hT, h1, h2]
  simp only [Bool.false_eq_true, if_false, if_true]
  exact Iff.rfl
