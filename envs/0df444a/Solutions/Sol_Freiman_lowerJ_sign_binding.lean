-- Prove2me | solution 1 for Freiman.lowerJ_sign_binding
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:15:45.877487+00:00
-- url     : https://prove2.me/submissions/8c9c189f-beb7-4e44-8cb2-b6f63815e531

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
theorem v_t_13 : prefixEval ([1, 3]:List ℕ+) lowerTau = ((1:ℝ)/2) + ((1:ℝ)/6) * (Real.sqrt 3) :=
  pe_step 1 [3] lowerTau (Real.sqrt 3) ((1:ℝ)/2) ((1:ℝ)/6) (2:ℝ) (-1:ℝ) (1:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/6)) * hs3)
theorem v_t_213 : prefixEval ([2, 1, 3]:List ℕ+) lowerTau = ((15:ℝ)/37) + ((-1:ℝ)/37) * (Real.sqrt 3) :=
  pe_step 2 [1, 3] lowerTau (Real.sqrt 3) ((15:ℝ)/37) ((-1:ℝ)/37) ((1:ℝ)/2) ((1:ℝ)/6) (2:ℝ) (by norm_num) v_t_13 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/222)) * hs3)
theorem v_t_1213 : prefixEval ([1, 2, 1, 3]:List ℕ+) lowerTau = ((52:ℝ)/73) + ((1:ℝ)/73) * (Real.sqrt 3) :=
  pe_step 1 [2, 1, 3] lowerTau (Real.sqrt 3) ((52:ℝ)/73) ((1:ℝ)/73) ((15:ℝ)/37) ((-1:ℝ)/37) (1:ℝ) (by norm_num) v_t_213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/2701)) * hs3)
theorem th90 : lowerTheta 90 = ((52:ℝ)/73) + ((1:ℝ)/73) * (Real.sqrt 3) := by
  have h : lowerTheta 90 = prefixEval ([1, 2, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_1213]
theorem th30 : lowerTheta 30 = ((15:ℝ)/37) + ((-1:ℝ)/37) * (Real.sqrt 3) := by
  have h : lowerTheta 30 = prefixEval ([2, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_213]
theorem v_t_23 : prefixEval ([2, 3]:List ℕ+) lowerTau = ((4:ℝ)/13) + ((1:ℝ)/13) * (Real.sqrt 3) :=
  pe_step 2 [3] lowerTau (Real.sqrt 3) ((4:ℝ)/13) ((1:ℝ)/13) (2:ℝ) (-1:ℝ) (2:ℝ) (by norm_num) v_t_3 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/13)) * hs3)
theorem th63 : lowerTheta 63 = ((4:ℝ)/13) + ((1:ℝ)/13) * (Real.sqrt 3) := by
  have h : lowerTheta 63 = prefixEval ([2, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_23]
theorem v_t_113 : prefixEval ([1, 1, 3]:List ℕ+) lowerTau = ((9:ℝ)/13) + ((-1:ℝ)/13) * (Real.sqrt 3) :=
  pe_step 1 [1, 3] lowerTau (Real.sqrt 3) ((9:ℝ)/13) ((-1:ℝ)/13) ((1:ℝ)/2) ((1:ℝ)/6) (1:ℝ) (by norm_num) v_t_13 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/78)) * hs3)
theorem th66 : lowerTheta 66 = ((9:ℝ)/13) + ((-1:ℝ)/13) * (Real.sqrt 3) := by
  have h : lowerTheta 66 = prefixEval ([1, 1, 3]:List ℕ+) lowerTau := rfl
  rw [h, v_t_113]
theorem v_t_31213 : prefixEval ([3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((271:ℝ)/1006) + ((-1:ℝ)/1006) * (Real.sqrt 3) :=
  pe_step 3 [1, 2, 1, 3] lowerTau (Real.sqrt 3) ((271:ℝ)/1006) ((-1:ℝ)/1006) ((52:ℝ)/73) ((1:ℝ)/73) (3:ℝ) (by norm_num) v_t_1213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/73438)) * hs3)
theorem v_t_331213 : prefixEval ([3, 3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((3289:ℝ)/10753) + ((1:ℝ)/10753) * (Real.sqrt 3) :=
  pe_step 3 [3, 1, 2, 1, 3] lowerTau (Real.sqrt 3) ((3289:ℝ)/10753) ((1:ℝ)/10753) ((271:ℝ)/1006) ((-1:ℝ)/1006) (3:ℝ) (by norm_num) v_t_31213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/10817518)) * hs3)
theorem pD : prefixEval ([3, 3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((3289:ℝ)/10753) + ((1:ℝ)/10753) * (Real.sqrt 3) := v_t_331213
theorem v_t_333 : prefixEval ([3, 3, 3]:List ℕ+) lowerTau = ((71:ℝ)/229) + ((-1:ℝ)/229) * (Real.sqrt 3) :=
  pe_step 3 [3, 3] lowerTau (Real.sqrt 3) ((71:ℝ)/229) ((-1:ℝ)/229) ((5:ℝ)/22) ((1:ℝ)/22) (3:ℝ) (by norm_num) v_t_33 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/5038)) * hs3)
theorem pIA : prefixEval ([3, 3, 3]:List ℕ+) lowerTau = ((71:ℝ)/229) + ((-1:ℝ)/229) * (Real.sqrt 3) := v_t_333
theorem v_t_3213 : prefixEval ([3, 2, 1, 3]:List ℕ+) lowerTau = ((42:ℝ)/143) + ((1:ℝ)/429) * (Real.sqrt 3) :=
  pe_step 3 [2, 1, 3] lowerTau (Real.sqrt 3) ((42:ℝ)/143) ((1:ℝ)/429) ((15:ℝ)/37) ((-1:ℝ)/37) (3:ℝ) (by norm_num) v_t_213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/15873)) * hs3)
theorem v_t_33213 : prefixEval ([3, 3, 2, 1, 3]:List ℕ+) lowerTau = ((1413:ℝ)/4654) + ((-1:ℝ)/4654) * (Real.sqrt 3) :=
  pe_step 3 [3, 2, 1, 3] lowerTau (Real.sqrt 3) ((1413:ℝ)/4654) ((-1:ℝ)/4654) ((42:ℝ)/143) ((1:ℝ)/429) (3:ℝ) (by norm_num) v_t_3213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/1996566)) * hs3)
theorem pIC : prefixEval ([3, 3, 2, 1, 3]:List ℕ+) lowerTau = ((1413:ℝ)/4654) + ((-1:ℝ)/4654) * (Real.sqrt 3) := v_t_33213
theorem v_t_3331213 : prefixEval ([3, 3, 3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((35548:ℝ)/117517) + ((-1:ℝ)/117517) * (Real.sqrt 3) :=
  pe_step 3 [3, 3, 1, 2, 1, 3] lowerTau (Real.sqrt 3) ((35548:ℝ)/117517) ((-1:ℝ)/117517) ((3289:ℝ)/10753) ((1:ℝ)/10753) (3:ℝ) (by norm_num) v_t_331213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/1263660301)) * hs3)
theorem v_t_33331213 : prefixEval ([3, 3, 3, 3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((388099:ℝ)/1281694) + ((1:ℝ)/1281694) * (Real.sqrt 3) :=
  pe_step 3 [3, 3, 3, 1, 2, 1, 3] lowerTau (Real.sqrt 3) ((388099:ℝ)/1281694) ((1:ℝ)/1281694) ((35548:ℝ)/117517) ((-1:ℝ)/117517) (3:ℝ) (by norm_num) v_t_3331213 (by linarith [sq3lo, sq3hi])
    (by linear_combination (((-1:ℝ)/150620833798)) * hs3)
theorem pID : prefixEval ([3, 3, 3, 3, 1, 2, 1, 3]:List ℕ+) lowerTau = ((388099:ℝ)/1281694) + ((1:ℝ)/1281694) * (Real.sqrt 3) := v_t_33331213

theorem hA : lowerJA = (2:ℝ) + (-1:ℝ) * (Real.sqrt 3) := th3
theorem hA2 : lowerJA2 = ((5:ℝ)/22) + ((1:ℝ)/22) * (Real.sqrt 3) := th25
theorem hB : lowerJB = ((52:ℝ)/73) + ((1:ℝ)/73) * (Real.sqrt 3) := th90
theorem hC : lowerJC = ((15:ℝ)/37) + ((-1:ℝ)/37) * (Real.sqrt 3) := th30
theorem hE : lowerJE = ((4:ℝ)/13) + ((1:ℝ)/13) * (Real.sqrt 3) := th63
theorem hX : lowerJX = ((9:ℝ)/13) + ((-1:ℝ)/13) * (Real.sqrt 3) := th66
theorem hD : lowerJD = ((3289:ℝ)/10753) + ((1:ℝ)/10753) * (Real.sqrt 3) := v_t_331213
theorem hIA : lowerJIter 2 lowerJA = ((71:ℝ)/229) + ((-1:ℝ)/229) * (Real.sqrt 3) := v_t_333
theorem hIC : lowerJIter 2 lowerJC = ((1413:ℝ)/4654) + ((-1:ℝ)/4654) * (Real.sqrt 3) := v_t_33213
theorem hID : lowerJIter 2 lowerJD = ((388099:ℝ)/1281694) + ((1:ℝ)/1281694) * (Real.sqrt 3) := v_t_33331213
theorem hCoeff : lowerJCoeff = ((-17359:ℝ)/1532) + ((10663:ℝ)/1532) * (Real.sqrt 3) := by
  unfold lowerJCoeff
  rw [hD, hA, hC, div_eq_iff (by linarith [sq3lo, sq3hi])]
  linear_combination (((57526885:ℝ)/304761526)) * hs3
theorem c0 : certFieldVal ⟨(-1/39:ℚ),(1/13:ℚ),0,0⟩ = lowerJE-1/3 := by
  simp only [certFieldVal]; push_cast; rw [hE]; ring
theorem c1 : certFieldVal ⟨(14/39:ℚ),(-1/13:ℚ),0,0⟩ = lowerJX-1/3 := by
  simp only [certFieldVal]; push_cast; rw [hX]; ring
theorem c2 : certFieldVal ⟨(-179/110:ℚ),(21/22:ℚ),0,0⟩ = 3/5-lowerJA-lowerJA2 := by
  simp only [certFieldVal]; push_cast; rw [hA2, hA]; ring
theorem c3 : certFieldVal ⟨(-251/1100:ℚ),(3/22:ℚ),0,0⟩ = 9/100-lowerJA*lowerJA2 := by
  simp only [certFieldVal]; push_cast; rw [hA2, hA]; linear_combination (((-1:ℝ)/22)) * hs3
theorem c4 : certFieldVal ⟨(30501883/3007002635:ℚ),0,0,0⟩ = 4/5-475020045/601400527 := by
  simp only [certFieldVal, lowerJPhi]; push_cast; norm_num
theorem c5 : certFieldVal ⟨(176/1805:ℚ),0,0,0⟩ = (18/19)^2-4/5 := by
  simp only [certFieldVal, lowerJPhi]; push_cast; norm_num
theorem c6 : certFieldVal ⟨(2584/12555:ℚ),0,0,0⟩ = 19/5-(19/18)^2/(31/100) := by
  simp only [certFieldVal, lowerJPhi]; push_cast; norm_num
theorem c7 : certFieldVal ⟨(-18217/10753:ℚ),(10754/10753:ℚ),0,0⟩ = lowerJD-lowerJA := by
  simp only [certFieldVal]; push_cast; rw [hA, hD]; ring
theorem c8 : certFieldVal ⟨(39602/397861:ℚ),(-10790/397861:ℚ),0,0⟩ = lowerJC-lowerJD := by
  simp only [certFieldVal]; push_cast; rw [hC, hD]; ring
theorem c9 : certFieldVal ⟨(829/2701:ℚ),(110/2701:ℚ),0,0⟩ = lowerJB-lowerJC := by
  simp only [certFieldVal]; push_cast; rw [hB, hC]; ring
theorem c10 : certFieldVal ⟨(-59/37:ℚ),(36/37:ℚ),0,0⟩ = lowerJC-lowerJA := by
  simp only [certFieldVal]; push_cast; rw [hA, hC]; ring
theorem c11 : certFieldVal ⟨(6725/16717:ℚ),(302/16717:ℚ),0,0⟩ = lowerJB-lowerJIter 2 lowerJA := by
  simp only [certFieldVal]; push_cast; rw [hIA, hB]; ring
theorem c12 : certFieldVal ⟨(138859/339742:ℚ),(4727/339742:ℚ),0,0⟩ = lowerJB-lowerJIter 2 lowerJC := by
  simp only [certFieldVal]; push_cast; rw [hIC, hB]; ring
theorem c13 : certFieldVal ⟨(8766/5329:ℚ),(323/5329:ℚ),0,0⟩ = lowerJB^2+3*lowerJB-1 := by
  simp only [certFieldVal]; push_cast; rw [hB]; linear_combination (((-1:ℝ)/5329)) * hs3
theorem c14 : certFieldVal ⟨(921/114500:ℚ),(-1/229:ℚ),0,0⟩ = lowerJIter 2 lowerJA-151/500 := by
  simp only [certFieldVal]; push_cast; rw [hIA]; ring
theorem c15 : certFieldVal ⟨(-1613/229000:ℚ),(1/229:ℚ),0,0⟩ = 303/1000-lowerJIter 2 lowerJA := by
  simp only [certFieldVal]; push_cast; rw [hIA]; ring
theorem c16 : certFieldVal ⟨(256853/320423500:ℚ),(1/1281694:ℚ),0,0⟩ = lowerJIter 2 lowerJD-151/500 := by
  simp only [certFieldVal]; push_cast; rw [hID]; ring
theorem c17 : certFieldVal ⟨(127141/640847000:ℚ),(-1/1281694:ℚ),0,0⟩ = 303/1000-lowerJIter 2 lowerJD := by
  simp only [certFieldVal]; push_cast; rw [hID]; ring
theorem c18 : certFieldVal ⟨(1873/1163500:ℚ),(-1/4654:ℚ),0,0⟩ = lowerJIter 2 lowerJC-151/500 := by
  simp only [certFieldVal]; push_cast; rw [hIC]; ring
theorem c19 : certFieldVal ⟨(227/581750:ℚ),(1/4654:ℚ),0,0⟩ = 38/125-lowerJIter 2 lowerJC := by
  simp only [certFieldVal]; push_cast; rw [hIC]; ring
theorem c20 : certFieldVal ⟨(256853/320423500:ℚ),(1/1281694:ℚ),0,0⟩ = lowerJIter 2 lowerJD-151/500 := by
  simp only [certFieldVal]; push_cast; rw [hID]; ring
theorem c21 : certFieldVal ⟨(191997/160211750:ℚ),(-1/1281694:ℚ),0,0⟩ = 38/125-lowerJIter 2 lowerJD := by
  simp only [certFieldVal]; push_cast; rw [hID]; ring
theorem c22 : certFieldVal ⟨(1247/1651500:ℚ),0,0,0⟩ = lowerJPhi (303/1000)-151/500 := by
  simp only [certFieldVal, lowerJPhi]; push_cast; norm_num
theorem c23 : certFieldVal ⟨(253/1651000:ℚ),0,0,0⟩ = 303/1000-lowerJPhi (151/500) := by
  simp only [certFieldVal, lowerJPhi]; push_cast; norm_num
theorem c24 : certFieldVal ⟨(137/206500:ℚ),0,0,0⟩ = lowerJPhi (38/125)-151/500 := by
  simp only [certFieldVal, lowerJPhi]; push_cast; norm_num
theorem c25 : certFieldVal ⟨(238/206375:ℚ),0,0,0⟩ = 38/125-lowerJPhi (151/500) := by
  simp only [certFieldVal, lowerJPhi]; push_cast; norm_num
theorem c26 : certFieldVal ⟨(-3366936/239375:ℚ),(15552029/1915000:ℚ),0,0⟩ = lowerJCoeff*(1+(3/10)*lowerJC)-(371/500)*(1+(3/10)*lowerJA) := by
  simp only [certFieldVal]; push_cast; rw [hCoeff, hA, hC]; linear_combination (((31989:ℝ)/566840)) * hs3
theorem c27 : certFieldVal ⟨(-410392/28725:ℚ),(789953/95750:ℚ),0,0⟩ = lowerJCoeff*(1+(1/3)*lowerJC)-(371/500)*(1+(1/3)*lowerJA) := by
  simp only [certFieldVal]; push_cast; rw [hCoeff, hA, hC]; linear_combination (((10663:ℝ)/170052)) * hs3

theorem solution : ∀ i : Fin 28, certFieldVal (lowerJSignFields i) = lowerJSigns i := by
  intro i
  fin_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7
  · exact c8
  · exact c9
  · exact c10
  · exact c11
  · exact c12
  · exact c13
  · exact c14
  · exact c15
  · exact c16
  · exact c17
  · exact c18
  · exact c19
  · exact c20
  · exact c21
  · exact c22
  · exact c23
  · exact c24
  · exact c25
  · exact c26
  · exact c27
