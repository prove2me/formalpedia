-- Prove2me | solution 1 for Freiman.lowerJ_equal_constants
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:12:28.159204+00:00
-- url     : https://prove2.me/submissions/31d6657e-db7f-4f59-ba92-67a634ae51d5

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases
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
theorem v_t_13 : prefixEval ([1, 3]:List ℕ+) lowerTau = ((1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 3) :=
  pe_step 1 [3] lowerTau (Real.sqrt 3) ((1:ℝ)/2) ((1:ℝ)/6) (2:ℝ) (-1:ℝ) (1:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/6)) * hs3)
theorem v_t_113 : prefixEval ([1, 1, 3]:List ℕ+) lowerTau = ((9:ℝ)/13) + ((-1:ℝ)/13) * (Real.sqrt 3) :=
  pe_step 1 [1, 3] lowerTau (Real.sqrt 3) ((9:ℝ)/13) ((-1:ℝ)/13) ((1:ℝ)/2) ((1:ℝ)/6) (1:ℝ) (by norm_num) v_t_13 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/78)) * hs3)
theorem th66 : lowerTheta 66 = ((9:ℝ)/13) + ((-1:ℝ)/13) * (Real.sqrt 3) := by
  have h : lowerTheta 66 = prefixEval ([1, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_113]
theorem v_t_23 : prefixEval ([2, 3]:List ℕ+) lowerTau = ((4:ℝ)/13) + ((1:ℝ)/13) * (Real.sqrt 3) :=
  pe_step 2 [3] lowerTau (Real.sqrt 3) ((4:ℝ)/13) ((1:ℝ)/13) (2:ℝ) (-1:ℝ) (2:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/13)) * hs3)
theorem th63 : lowerTheta 63 = ((4:ℝ)/13) + ((1:ℝ)/13) * (Real.sqrt 3) := by
  have h : lowerTheta 63 = prefixEval ([2, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_23]
theorem v_t_213 : prefixEval ([2, 1, 3]:List ℕ+) lowerTau = ((15:ℝ)/37) + ((-1:ℝ)/37) * (Real.sqrt 3) :=
  pe_step 2 [1, 3] lowerTau (Real.sqrt 3) ((15:ℝ)/37) ((-1:ℝ)/37) ((1:ℝ)/2) ((1:ℝ)/6) (2:ℝ) (by norm_num) v_t_13 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/222)) * hs3)
theorem v_t_1213 : prefixEval ([1, 2, 1, 3]:List ℕ+) lowerTau = ((52:ℝ)/73) + ((1:ℝ)/73) * (Real.sqrt 3) :=
  pe_step 1 [2, 1, 3] lowerTau (Real.sqrt 3) ((52:ℝ)/73) ((1:ℝ)/73) ((15:ℝ)/37) ((-1:ℝ)/37) (1:ℝ) (by norm_num) v_t_213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/2701)) * hs3)
theorem th90 : lowerTheta 90 = ((52:ℝ)/73) + ((1:ℝ)/73) * (Real.sqrt 3) := by
  have h : lowerTheta 90 = prefixEval ([1, 2, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_1213]
theorem th3 : lowerTheta 3 = (2:ℝ) + (-1:ℝ) * (Real.sqrt 3) := by
  have h : lowerTheta 3 = prefixEval ([3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_3]
theorem v_a_e : prefixEval ([]:List ℕ+) lowerAlpha = ((-1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 21) := by
  simp only [prefixEval, lowerAlpha]; ring
theorem v_a_3 : prefixEval ([3]:List ℕ+) lowerAlpha = ((15:ℝ)/34) + ((-1:ℝ)/34) * (Real.sqrt 21) :=
  pe_step 3 [] lowerAlpha (Real.sqrt 21) ((15:ℝ)/34) ((-1:ℝ)/34) ((-1:ℝ)/2) ((1:ℝ)/6) (3:ℝ) (by norm_num) v_a_e (by linarith [s21lo, s21hi])
    (by linear_combination (((-1:ℝ)/204)) * hs21)
theorem v_a_13 : prefixEval ([1, 3]:List ℕ+) lowerAlpha = ((7:ℝ)/10) + ((1:ℝ)/70) * (Real.sqrt 21) :=
  pe_step 1 [3] lowerAlpha (Real.sqrt 21) ((7:ℝ)/10) ((1:ℝ)/70) ((15:ℝ)/34) ((-1:ℝ)/34) (1:ℝ) (by norm_num) v_a_3 (by linarith [s21lo, s21hi])
    (by linear_combination (((-1:ℝ)/2380)) * hs21)
theorem v_a_113 : prefixEval ([1, 1, 3]:List ℕ+) lowerAlpha = ((119:ℝ)/202) + ((-1:ℝ)/202) * (Real.sqrt 21) :=
  pe_step 1 [1, 3] lowerAlpha (Real.sqrt 21) ((119:ℝ)/202) ((-1:ℝ)/202) ((7:ℝ)/10) ((1:ℝ)/70) (1:ℝ) (by norm_num) v_a_13 (by linarith [s21lo, s21hi])
    (by linear_combination (((-1:ℝ)/14140)) * hs21)
theorem th68 : lowerTheta 68 = ((119:ℝ)/202) + ((-1:ℝ)/202) * (Real.sqrt 21) := by
  have h : lowerTheta 68 = prefixEval ([1, 1, 3]:List ℕ+) lowerAlpha := rfl
  rw [h, v_a_113]
theorem v_b_e : prefixEval ([]:List ℕ+) lowerBeta = ((-3:ℝ)/2) + ((1:ℝ)/2) * (Real.sqrt 21) := by
  simp only [prefixEval, lowerBeta]; ring
theorem v_b_1 : prefixEval ([1]:List ℕ+) lowerBeta = ((1:ℝ)/10) + ((1:ℝ)/10) * (Real.sqrt 21) :=
  pe_step 1 [] lowerBeta (Real.sqrt 21) ((1:ℝ)/10) ((1:ℝ)/10) ((-3:ℝ)/2) ((1:ℝ)/2) (1:ℝ) (by norm_num) v_b_e (by linarith [s21lo, s21hi])
    (by linear_combination (((1:ℝ)/20)) * hs21)
theorem th65 : lowerTheta 65 = ((1:ℝ)/10) + ((1:ℝ)/10) * (Real.sqrt 21) := by
  have h : lowerTheta 65 = prefixEval ([1]:List ℕ+) lowerBeta := rfl
  rw [h, v_b_1]
theorem th28 : lowerTheta 28 = ((15:ℝ)/34) + ((-1:ℝ)/34) * (Real.sqrt 21) := by
  have h : lowerTheta 28 = prefixEval ([3]:List ℕ+) lowerAlpha := rfl
  rw [h, v_a_3]
theorem th1 : lowerTheta 1 = ((-1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 21) := by
  have h : lowerTheta 1 = prefixEval ([]:List ℕ+) lowerAlpha := rfl
  rw [h, v_a_e]
theorem th30 : lowerTheta 30 = ((15:ℝ)/37) + ((-1:ℝ)/37) * (Real.sqrt 3) := by
  have h : lowerTheta 30 = prefixEval ([2, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_213]
theorem solution : (lowerTheta 66-lowerTheta 63)/(lowerTheta 90-lowerTheta 3) < (253/1000:ℝ) ∧ (7/5:ℝ)*(lowerTheta 68-lowerTheta 65)/(lowerTheta 28-lowerTheta 1) < (269/1000:ℝ) ∧ lowerTheta 3 < lowerTheta 30 ∧ lowerTheta 30 < lowerTheta 63 ∧ lowerTheta 63 < lowerTheta 66 ∧ lowerTheta 66 < lowerTheta 90 ∧ lowerTheta 65 < lowerTheta 68 ∧ lowerTheta 1 < lowerTheta 28 ∧ (19/5:ℝ)*(253/1000)*(26/25)<1 ∧ (269/1000:ℝ)<(253/1000)*(133/125) := by
  rw [th66, th63, th90, th3, th68, th65, th28, th1, th30]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by linarith [sq3lo, sq3hi])]; linarith [sq3lo, sq3hi]
  · rw [div_lt_iff₀ (by linarith [s21lo, s21hi])]; linarith [s21lo, s21hi]
  · linarith [sq3lo, sq3hi]
  · linarith [sq3lo, sq3hi]
  · linarith [sq3lo, sq3hi]
  · linarith [sq3lo, sq3hi]
  · linarith [s21lo, s21hi]
  · linarith [s21lo, s21hi]
  · norm_num
  · norm_num
