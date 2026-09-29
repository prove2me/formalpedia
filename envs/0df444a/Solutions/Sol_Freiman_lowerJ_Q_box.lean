-- Prove2me | solution 1 for Freiman.lowerJ_Q_box
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:08:14.631974+00:00
-- url     : https://prove2.me/submissions/5f39d58b-64e0-46b8-b07f-0a77158a9d90

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
theorem th3 : lowerTheta 3 = (2:ℝ) + (-1:ℝ) * (Real.sqrt 3) := by
  have h : lowerTheta 3 = prefixEval ([3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_3]
theorem v_t_33 : prefixEval ([3, 3]:List ℕ+) lowerTau = ((5:ℝ)/22) + ((1:ℝ)/22) * (Real.sqrt 3) :=
  pe_step 3 [3] lowerTau (Real.sqrt 3) ((5:ℝ)/22) ((1:ℝ)/22) (2:ℝ) (-1:ℝ) (3:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/22)) * hs3)
theorem th25 : lowerTheta 25 = ((5:ℝ)/22) + ((1:ℝ)/22) * (Real.sqrt 3) := by
  have h : lowerTheta 25 = prefixEval ([3, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_33]
theorem v_a_e : prefixEval ([]:List ℕ+) lowerAlpha = ((-1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 21) := by
  simp only [prefixEval, lowerAlpha]; ring
theorem v_a_3 : prefixEval ([3]:List ℕ+) lowerAlpha = ((15:ℝ)/34) + ((-1:ℝ)/34) * (Real.sqrt 21) :=
  pe_step 3 [] lowerAlpha (Real.sqrt 21) ((15:ℝ)/34) ((-1:ℝ)/34) ((-1:ℝ)/2) ((1:ℝ)/6) (3:ℝ) (by norm_num) v_a_e (by linarith [s21lo, s21hi])
    (by linear_combination (((-1:ℝ)/204)) * hs21)
theorem pA3 : prefixEval ([3]:List ℕ+) lowerAlpha = ((15:ℝ)/34) + ((-1:ℝ)/34) * (Real.sqrt 21) := v_a_3
theorem v_b_e : prefixEval ([]:List ℕ+) lowerBeta = ((-3:ℝ)/2) + ((1:ℝ)/2) * (Real.sqrt 21) := by
  simp only [prefixEval, lowerBeta]; ring
theorem v_b_3 : prefixEval ([3]:List ℕ+) lowerBeta = ((-1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 21) :=
  pe_step 3 [] lowerBeta (Real.sqrt 21) ((-1:ℝ)/2) ((1:ℝ)/6) ((-3:ℝ)/2) ((1:ℝ)/2) (3:ℝ) (by norm_num) v_b_e (by linarith [s21lo, s21hi])
    (by linear_combination (((1:ℝ)/12)) * hs21)
theorem pB3 : prefixEval ([3]:List ℕ+) lowerBeta = ((-1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 21) := v_b_3

theorem N2 (r : ℝ) (h1 : 1/4 ≤ r) (h2 : r ≤ 4/5) :
    (1+r*(1/3))^2 ≤ (1065/1000)*((1+r*(306394/1000000))*(1+r*(263762/1000000))) := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ 4/5 - r)]
theorem M2 (s : ℝ) (h1 : 1/4 ≤ s) (h2 : s ≤ 4/5) :
    (1+s*(306395/1000000))*(1+s*(263763/1000000)) ≤ (9935/10000)*(1+s*(3/10))^2 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s) (by linarith : (0:ℝ) ≤ s - 1/4)]

theorem solution (hn : lowerJSignFacts) (r s q tau : ℝ) (hd : lowerJDomain r s q) (ht : (3/10:ℝ) ≤ tau ∧ tau ≤ (1/3:ℝ)) : (31/100:ℝ) < lowerJQ r s q tau ∧ lowerJQ r s q tau < (4/5:ℝ) := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hs1, hs2⟩, hq1, hq2⟩ := hd
  obtain ⟨ht1, ht2⟩ := ht
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have s0 : lowerJSigns 0 = lowerJE - 1/3 := rfl
  have s1 : lowerJSigns 1 = lowerJX - 1/3 := rfl
  have s2 : lowerJSigns 2 = 3/5 - lowerJA - lowerJA2 := rfl
  have s3 : lowerJSigns 3 = 9/100 - lowerJA*lowerJA2 := rfl
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  rw [s0] at h0
  rw [s1] at h1
  rw [s2] at h2
  rw [s3] at h3
  clear hn s0 s1 s2 s3
  have Apos : 0 < lowerJA := by unfold lowerJA; rw [th3]; linarith [sq3lo, sq3hi]
  have A2pos : 0 < lowerJA2 := by unfold lowerJA2; rw [th25]; linarith [sq3lo, sq3hi]
  have Epos : 0 < lowerJE := by linarith
  have Xpos : 0 < lowerJX := by linarith
  have rt : 0 ≤ r*tau := mul_nonneg hr0.le (by linarith)
  have st : 0 ≤ s*tau := mul_nonneg hs0.le (by linarith)
  have rA : 0 ≤ r*lowerJA := mul_nonneg hr0.le Apos.le
  have rA2 : 0 ≤ r*lowerJA2 := mul_nonneg hr0.le A2pos.le
  have sE : 0 ≤ s*lowerJE := mul_nonneg hs0.le Epos.le
  have sX : 0 ≤ s*lowerJX := mul_nonneg hs0.le Xpos.le
  unfold lowerJQ
  unfold lowerJH7 lowerJH at hq1
  unfold lowerJHStar lowerJH at hq2
  have pV : 0 < (1+r*lowerJA)*(1+r*lowerJA2) := mul_pos (by linarith) (by linarith)
  have hqV : (31/100)*(1+s*lowerJE)*(1+s*lowerJX) ≤ q * ((1+r*lowerJA)*(1+r*lowerJA2)) :=
    (div_le_iff₀ pV).1 hq1
  have hS : 0 < (1+s*tau)^2 := pow_pos (by linarith) 2
  have hT : 0 < (1+r*tau)^2 := pow_pos (by linarith) 2
  have qpos : 0 < q := by
    have hnum : 0 < (31/100)*(1+s*lowerJE)*(1+s*lowerJX) :=
      mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    have : 0 < (31/100)*(1+s*lowerJE)*(1+s*lowerJX)/((1+r*lowerJA)*(1+r*lowerJA2)) := div_pos hnum pV
    linarith
  constructor
  · rw [lt_div_iff₀ hS]
    have hU : (1+s*tau)^2 < (1+s*lowerJE)*(1+s*lowerJX) := by
      have e1 : 1+s*tau < 1+s*lowerJE := by
        have := mul_lt_mul_of_pos_left (show tau < lowerJE by linarith) hs0; linarith
      have e2 : 1+s*tau < 1+s*lowerJX := by
        have := mul_lt_mul_of_pos_left (show tau < lowerJX by linarith) hs0; linarith
      rw [sq]
      exact mul_lt_mul'' e1 e2 (by linarith) (by linarith)
    have hV : (1+r*lowerJA)*(1+r*lowerJA2) < (1+r*tau)^2 := by
      have e1 : r*(lowerJA+lowerJA2) < r*(3/5) := mul_lt_mul_of_pos_left (by linarith) hr0
      have e2 : r^2*(lowerJA*lowerJA2) < r^2*(9/100) := mul_lt_mul_of_pos_left (by linarith) (by positivity)
      have e3 : (1+r*(3/10))^2 ≤ (1+r*tau)^2 := by
        apply pow_le_pow_left₀ (by linarith)
        have := mul_le_mul_of_nonneg_left ht1 hr0.le
        linarith
      have ex1 : (1+r*lowerJA)*(1+r*lowerJA2) = 1 + r*(lowerJA+lowerJA2) + r^2*(lowerJA*lowerJA2) := by ring
      have ex2 : (1+r*(3/10))^2 = 1 + r*(3/5) + r^2*(9/100) := by ring
      rw [ex1]
      linarith [e1, e2, e3, ex2]
    calc (31/100)*(1+s*tau)^2 < (31/100)*((1+s*lowerJE)*(1+s*lowerJX)) :=
          mul_lt_mul_of_pos_left hU (by norm_num)
      _ ≤ q*((1+r*lowerJA)*(1+r*lowerJA2)) := by linarith [hqV]
      _ < q*(1+r*tau)^2 := mul_lt_mul_of_pos_left hV qpos
  · rw [div_lt_iff₀ hS]
    have ha1 : (306394/1000000:ℝ) ≤ prefixEval [3] lowerAlpha ∧ prefixEval [3] lowerAlpha ≤ (306395/1000000:ℝ) := by
      rw [pA3]; constructor <;> linarith [s21lo, s21hi]
    have hb1 : (263762/1000000:ℝ) ≤ prefixEval [3] lowerBeta ∧ prefixEval [3] lowerBeta ≤ (263763/1000000:ℝ) := by
      rw [pB3]; constructor <;> linarith [s21lo, s21hi]
    generalize prefixEval [3] lowerAlpha = a at ha1 hq2
    generalize prefixEval [3] lowerBeta = b at hb1 hq2
    obtain ⟨ha1, ha2⟩ := ha1
    obtain ⟨hb1, hb2⟩ := hb1
    have ra1 := mul_le_mul_of_nonneg_left ha1 hr0.le
    have ra2 := mul_le_mul_of_nonneg_left ha2 hr0.le
    have rb1 := mul_le_mul_of_nonneg_left hb1 hr0.le
    have rb2 := mul_le_mul_of_nonneg_left hb2 hr0.le
    have sa1 := mul_le_mul_of_nonneg_left ha1 hs0.le
    have sa2 := mul_le_mul_of_nonneg_left ha2 hs0.le
    have sb1 := mul_le_mul_of_nonneg_left hb1 hs0.le
    have sb2 := mul_le_mul_of_nonneg_left hb2 hs0.le
    have hN : 0 < (1+r*a)*(1+r*b) := mul_pos (by linarith) (by linarith)
    have hM : 0 < (1+s*a)*(1+s*b) := mul_pos (by linarith) (by linarith)
    have hqN : q * ((1+r*a)*(1+r*b)) < 5/7*(1+s*a)*(1+s*b) := (lt_div_iff₀ hN).1 hq2
    have f1 : (1+r*tau)^2 ≤ (1+r*(1/3))^2 := by
      apply pow_le_pow_left₀ (by linarith)
      have := mul_le_mul_of_nonneg_left ht2 hr0.le
      linarith
    have N1 : (1+r*(306394/1000000))*(1+r*(263762/1000000)) ≤ (1+r*a)*(1+r*b) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have f2 : (1+r*(1/3))^2 ≤ (1065/1000)*((1+r*a)*(1+r*b)) :=
      (N2 r hr1 hr2).trans (mul_le_mul_of_nonneg_left N1 (by norm_num))
    have M1 : (1+s*a)*(1+s*b) ≤ (1+s*(306395/1000000))*(1+s*(263763/1000000)) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have g1 : (1+s*a)*(1+s*b) ≤ (9935/10000)*(1+s*(3/10))^2 := M1.trans (M2 s hs1 hs2)
    have g2 : (1+s*(3/10))^2 ≤ (1+s*tau)^2 := by
      apply pow_le_pow_left₀ (by linarith)
      have := mul_le_mul_of_nonneg_left ht1 hs0.le
      linarith
    have step1 : q*((1+r*a)*(1+r*b))*(1+r*tau)^2 < 5/7*(1+s*a)*(1+s*b)*(1+r*tau)^2 :=
      mul_lt_mul_of_pos_right hqN hT
    have step2 : 5/7*(1+s*a)*(1+s*b)*(1+r*tau)^2 ≤ 5/7*(1+s*a)*(1+s*b)*((1065/1000)*((1+r*a)*(1+r*b))) :=
      mul_le_mul_of_nonneg_left (f1.trans f2) (by linarith [mul_pos hM (show (0:ℝ) < 5/7 by norm_num)])
    have step3 : (1+s*a)*(1+s*b)*((1065/1000)*((1+r*a)*(1+r*b))) ≤
        ((9935/10000)*(1+s*(3/10))^2)*((1065/1000)*((1+r*a)*(1+r*b))) :=
      mul_le_mul_of_nonneg_right g1 (by linarith)
    have step4 : (1+s*(3/10))^2*((1+r*a)*(1+r*b)) ≤ (1+s*tau)^2*((1+r*a)*(1+r*b)) :=
      mul_le_mul_of_nonneg_right g2 hN.le
    have key : q*(1+r*tau)^2*((1+r*a)*(1+r*b)) < 4/5*(1+s*tau)^2*((1+r*a)*(1+r*b)) := by
      linarith [step1, step2, step3, step4, mul_pos hS hN]
    exact lt_of_mul_lt_mul_right key hN.le
