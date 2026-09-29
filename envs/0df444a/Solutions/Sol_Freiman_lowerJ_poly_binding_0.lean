-- Prove2me | solution 1 for Freiman.lowerJ_poly_binding_0
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:13:16.081864+00:00
-- url     : https://prove2.me/submissions/31a40a75-4e2f-4d93-b25d-77aac6a1c8d8

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
theorem v_t_23 : prefixEval ([2, 3]:List ℕ+) lowerTau = ((4:ℝ)/13) + ((1:ℝ)/13) * (Real.sqrt 3) :=
  pe_step 2 [3] lowerTau (Real.sqrt 3) ((4:ℝ)/13) ((1:ℝ)/13) (2:ℝ) (-1:ℝ) (2:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/13)) * hs3)
theorem th63 : lowerTheta 63 = ((4:ℝ)/13) + ((1:ℝ)/13) * (Real.sqrt 3) := by
  have h : lowerTheta 63 = prefixEval ([2, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_23]
theorem v_t_13 : prefixEval ([1, 3]:List ℕ+) lowerTau = ((1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 3) :=
  pe_step 1 [3] lowerTau (Real.sqrt 3) ((1:ℝ)/2) ((1:ℝ)/6) (2:ℝ) (-1:ℝ) (1:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/6)) * hs3)
theorem v_t_113 : prefixEval ([1, 1, 3]:List ℕ+) lowerTau = ((9:ℝ)/13) + ((-1:ℝ)/13) * (Real.sqrt 3) :=
  pe_step 1 [1, 3] lowerTau (Real.sqrt 3) ((9:ℝ)/13) ((-1:ℝ)/13) ((1:ℝ)/2) ((1:ℝ)/6) (1:ℝ) (by norm_num) v_t_13 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/78)) * hs3)
theorem th66 : lowerTheta 66 = ((9:ℝ)/13) + ((-1:ℝ)/13) * (Real.sqrt 3) := by
  have h : lowerTheta 66 = prefixEval ([1, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_113]
theorem v_t_213 : prefixEval ([2, 1, 3]:List ℕ+) lowerTau = ((15:ℝ)/37) + ((-1:ℝ)/37) * (Real.sqrt 3) :=
  pe_step 2 [1, 3] lowerTau (Real.sqrt 3) ((15:ℝ)/37) ((-1:ℝ)/37) ((1:ℝ)/2) ((1:ℝ)/6) (2:ℝ) (by norm_num) v_t_13 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/222)) * hs3)
theorem v_t_1213 : prefixEval ([1, 2, 1, 3]:List ℕ+) lowerTau = ((52:ℝ)/73) + ((1:ℝ)/73) * (Real.sqrt 3) :=
  pe_step 1 [2, 1, 3] lowerTau (Real.sqrt 3) ((52:ℝ)/73) ((1:ℝ)/73) ((15:ℝ)/37) ((-1:ℝ)/37) (1:ℝ) (by norm_num) v_t_213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/2701)) * hs3)
theorem th90 : lowerTheta 90 = ((52:ℝ)/73) + ((1:ℝ)/73) * (Real.sqrt 3) := by
  have h : lowerTheta 90 = prefixEval ([1, 2, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_1213]
theorem v_b_e : prefixEval ([]:List ℕ+) lowerBeta = ((-3:ℝ)/2) + ((1:ℝ)/2) * (Real.sqrt 21) := by
  simp only [prefixEval, lowerBeta]; ring
theorem v_b_1 : prefixEval ([1]:List ℕ+) lowerBeta = ((1:ℝ)/10) + ((1:ℝ)/10) * (Real.sqrt 21) :=
  pe_step 1 [] lowerBeta (Real.sqrt 21) ((1:ℝ)/10) ((1:ℝ)/10) ((-3:ℝ)/2) ((1:ℝ)/2) (1:ℝ) (by norm_num) v_b_e (by linarith [s21lo, s21hi])
    (by linear_combination (((1:ℝ)/20)) * hs21)
theorem th65 : lowerTheta 65 = ((1:ℝ)/10) + ((1:ℝ)/10) * (Real.sqrt 21) := by
  have h : lowerTheta 65 = prefixEval ([1]:List ℕ+) lowerBeta := rfl
  rw [h, v_b_1]
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
theorem th28 : lowerTheta 28 = ((15:ℝ)/34) + ((-1:ℝ)/34) * (Real.sqrt 21) := by
  have h : lowerTheta 28 = prefixEval ([3]:List ℕ+) lowerAlpha := rfl
  rw [h, v_a_3]
theorem pA3 : prefixEval ([3]:List ℕ+) lowerAlpha = ((15:ℝ)/34) + ((-1:ℝ)/34) * (Real.sqrt 21) := v_a_3
theorem v_b_3 : prefixEval ([3]:List ℕ+) lowerBeta = ((-1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 21) :=
  pe_step 3 [] lowerBeta (Real.sqrt 21) ((-1:ℝ)/2) ((1:ℝ)/6) ((-3:ℝ)/2) ((1:ℝ)/2) (3:ℝ) (by norm_num) v_b_e (by linarith [s21lo, s21hi])
    (by linear_combination (((1:ℝ)/12)) * hs21)
theorem pB3 : prefixEval ([3]:List ℕ+) lowerBeta = ((-1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 21) := v_b_3
theorem v_t_33 : prefixEval ([3, 3]:List ℕ+) lowerTau = ((5:ℝ)/22) + ((1:ℝ)/22) * (Real.sqrt 3) :=
  pe_step 3 [3] lowerTau (Real.sqrt 3) ((5:ℝ)/22) ((1:ℝ)/22) (2:ℝ) (-1:ℝ) (3:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/22)) * hs3)
theorem pPhiA : prefixEval ([3, 3]:List ℕ+) lowerTau = ((5:ℝ)/22) + ((1:ℝ)/22) * (Real.sqrt 3) := v_t_33
theorem v_t_31213 : prefixEval ([3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((271:ℝ)/1006) + ((-1:ℝ)/1006) * (Real.sqrt 3) :=
  pe_step 3 [1, 2, 1, 3] lowerTau (Real.sqrt 3) ((271:ℝ)/1006) ((-1:ℝ)/1006) ((52:ℝ)/73) ((1:ℝ)/73) (3:ℝ) (by norm_num) v_t_1213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/73438)) * hs3)
theorem v_t_331213 : prefixEval ([3, 3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((3289:ℝ)/10753) + ((1:ℝ)/10753) * (Real.sqrt 3) :=
  pe_step 3 [3, 1, 2, 1, 3] lowerTau (Real.sqrt 3) ((3289:ℝ)/10753) ((1:ℝ)/10753) ((271:ℝ)/1006) ((-1:ℝ)/1006) (3:ℝ) (by norm_num) v_t_31213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/10817518)) * hs3)
theorem v_t_3331213 : prefixEval ([3, 3, 3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((35548:ℝ)/117517) + ((-1:ℝ)/117517) * (Real.sqrt 3) :=
  pe_step 3 [3, 3, 1, 2, 1, 3] lowerTau (Real.sqrt 3) ((35548:ℝ)/117517) ((-1:ℝ)/117517) ((3289:ℝ)/10753) ((1:ℝ)/10753) (3:ℝ) (by norm_num) v_t_331213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/1263660301)) * hs3)
theorem pPhiD : prefixEval ([3, 3, 3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((35548:ℝ)/117517) + ((-1:ℝ)/117517) * (Real.sqrt 3) := v_t_3331213
theorem v_t_3213 : prefixEval ([3, 2, 1, 3]:List ℕ+) lowerTau = ((42:ℝ)/143) + ((1:ℝ)/429) * (Real.sqrt 3) :=
  pe_step 3 [2, 1, 3] lowerTau (Real.sqrt 3) ((42:ℝ)/143) ((1:ℝ)/429) ((15:ℝ)/37) ((-1:ℝ)/37) (3:ℝ) (by norm_num) v_t_213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/15873)) * hs3)
theorem pPhiC : prefixEval ([3, 2, 1, 3]:List ℕ+) lowerTau = ((42:ℝ)/143) + ((1:ℝ)/429) * (Real.sqrt 3) := v_t_3213

theorem tval (c x0 x1 y0 y1 : CertField) (r s : ℝ) : certThresholdVal ⟨c,x0,x1,y0,y1⟩ r s =
    certFieldVal c * (1+s*certFieldVal y0)*(1+s*certFieldVal y1) / ((1+r*certFieldVal x0)*(1+r*certFieldVal x1)) := rfl

theorem phi_eq (x : ℝ) : lowerJPhi x = prefixEval [3] x := by
  unfold lowerJPhi; simp only [prefixEval]; norm_num

theorem hphiA : lowerJPhi lowerJA = ((5:ℝ)/22) + ((1:ℝ)/22) * (Real.sqrt 3) := by rw [phi_eq]; exact pPhiA
theorem hphiD : lowerJPhi lowerJD = ((35548:ℝ)/117517) + ((-1:ℝ)/117517) * (Real.sqrt 3) := by rw [phi_eq]; exact pPhiD
theorem hphiC : lowerJPhi lowerJC = ((42:ℝ)/143) + ((1:ℝ)/429) * (Real.sqrt 3) := by rw [phi_eq]; exact pPhiC
theorem hcoef : (((35548:ℝ)/117517) + ((-1:ℝ)/117517) * (Real.sqrt 3) - (((5:ℝ)/22) + ((1:ℝ)/22) * (Real.sqrt 3))) / (((42:ℝ)/143) + ((1:ℝ)/429) * (Real.sqrt 3) - (((35548:ℝ)/117517) + ((-1:ℝ)/117517) * (Real.sqrt 3))) = ((-2154:ℝ)/383) + ((5633:ℝ)/1532) * (Real.sqrt 3) := by
  rw [div_eq_iff (by linarith [sq3lo, sq3hi])]
  linear_combination (((-332194909:ℝ)/38617731438)) * hs3

theorem t1 : lowerTheta 1 = lowerAlpha := rfl
theorem t95 : lowerTheta 95 = lowerBeta := rfl
theorem fpos (x t : ℝ) (hx : 0 < x) (ht : 0 < t) : 0 < 1 + x*t := by nlinarith
theorem alpha_pos : 0 < lowerAlpha := by unfold lowerAlpha; linarith [s21lo]
theorem beta_pos : 0 < lowerBeta := by unfold lowerBeta; linarith [s21lo]
theorem th3_pos : 0 < lowerTheta 3 := by rw [th3]; linarith [sq3lo, sq3hi]
theorem th90_pos : 0 < lowerTheta 90 := by rw [th90]; linarith [sq3lo, sq3hi]
theorem th63_pos : 0 < lowerTheta 63 := by rw [th63]; linarith [sq3lo, sq3hi]
theorem th66_pos : 0 < lowerTheta 66 := by rw [th66]; linarith [sq3lo, sq3hi]
theorem th65_pos : 0 < lowerTheta 65 := by rw [th65]; linarith [s21lo, s21hi]
theorem th68_pos : 0 < lowerTheta 68 := by rw [th68]; linarith [s21lo, s21hi]
theorem th28_pos : 0 < lowerTheta 28 := by rw [th28]; linarith [s21lo, s21hi]

theorem key2 (P Q M N c : ℝ) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hN : 0 < N) :
    0 < c*M/N - P/Q ↔ (N*P)/(Q*M) < c := by
  rw [sub_pos, div_lt_div_iff₀ hQ hN, div_lt_iff₀ (mul_pos hQ hM)]
  constructor <;> intro h <;> linarith
theorem key3 (P Q M N c : ℝ) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hN : 0 < N) :
    0 < P/Q - c*M/N ↔ c < (N*P)/(Q*M) := by
  rw [sub_pos, div_lt_div_iff₀ hN hQ, lt_div_iff₀ (mul_pos hQ hM)]
  constructor <;> intro h <;> linarith

theorem solution (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) : 0 < lowerJPolyDifference 0 r s ↔ lowerJHStar r s < lowerJH1 r s := by
  have eH : lowerJPolyHigher 0 = ⟨⟨(-2154/383),(5633/1532),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(35548/117517),(-1/117517),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(35548/117517),(-1/117517),0,0⟩⟩ := rfl
  have eL : lowerJPolyLower 0 = ⟨⟨(5/7),0,0,0⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩ := rfl
  have vH : certThresholdVal (lowerJPolyHigher 0) r s = lowerJH1 r s := by
    rw [eH, tval]; unfold lowerJH1 lowerJH; rw [hphiA, hphiD, hphiC, hcoef]
    simp only [certFieldVal]; push_cast; ring
  have vL : certThresholdVal (lowerJPolyLower 0) r s = lowerJHStar r s := by
    rw [eL, tval]; unfold lowerJHStar lowerJH; rw [pA3, pB3]
    simp only [certFieldVal]; push_cast; ring
  unfold lowerJPolyDifference
  rw [vH, vL]
  exact sub_pos
