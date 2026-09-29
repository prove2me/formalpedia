-- Prove2me | solution 1 for Freiman.lowerHistory_theta_values
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-11T02:25:03.301153+00:00
-- url     : https://prove2.me/submissions/8546faea-0f37-477f-a25b-7db8ac5f8b5a

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option autoImplicit false

private theorem ar_surd_inverse (D a b c d : ℝ) (hD : 0 ≤ D)
    (h0 : a*c + D*b*d = 1) (h1 : a*d+b*c = 0) :
    (a+b*Real.sqrt D)⁻¹ = c+d*Real.sqrt D := by
  apply inv_eq_of_mul_eq_one_right
  calc
    (a+b*Real.sqrt D)*(c+d*Real.sqrt D) =
        a*c + D*b*d + (a*d+b*c)*Real.sqrt D := by
      have hs : (Real.sqrt D)^2 = D := Real.sq_sqrt hD
      calc
        _ = a*c + b*d*(Real.sqrt D)^2 + (a*d+b*c)*Real.sqrt D := by ring
        _ = _ := by rw [hs]; ring
    _ = 1 := by rw [h0, h1]; ring

private theorem ar_eval_0 : prefixEval [] lowerTau = (-1/1 : ℝ) + (1/1 : ℝ) * Real.sqrt 3 := by
  dsimp [prefixEval, lowerTau]
  ring

private theorem ar_eval_1 : prefixEval [3] lowerTau = (2/1 : ℝ) + (-1/1 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((3 : ℕ+) : ℕ) : ℝ) + prefixEval [] lowerTau) = _
  rw [ar_eval_0]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((3 : ℝ) + (-1/1 : ℝ)) (1/1 : ℝ)
      (2/1 : ℝ) (-1/1 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_2 : prefixEval [1,3] lowerTau = (1/2 : ℝ) + (1/6 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((1 : ℕ+) : ℕ) : ℝ) + prefixEval [3] lowerTau) = _
  rw [ar_eval_1]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((1 : ℝ) + (2/1 : ℝ)) (-1/1 : ℝ)
      (1/2 : ℝ) (1/6 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_3 : prefixEval [2,3] lowerTau = (4/13 : ℝ) + (1/13 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((2 : ℕ+) : ℕ) : ℝ) + prefixEval [3] lowerTau) = _
  rw [ar_eval_1]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((2 : ℝ) + (2/1 : ℝ)) (-1/1 : ℝ)
      (4/13 : ℝ) (1/13 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_4 : prefixEval [3,3] lowerTau = (5/22 : ℝ) + (1/22 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((3 : ℕ+) : ℕ) : ℝ) + prefixEval [3] lowerTau) = _
  rw [ar_eval_1]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((3 : ℝ) + (2/1 : ℝ)) (-1/1 : ℝ)
      (5/22 : ℝ) (1/22 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_5 : prefixEval [1,1,3] lowerTau = (9/13 : ℝ) + (-1/13 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((1 : ℕ+) : ℕ) : ℝ) + prefixEval [1,3] lowerTau) = _
  rw [ar_eval_2]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((1 : ℝ) + (1/2 : ℝ)) (1/6 : ℝ)
      (9/13 : ℝ) (-1/13 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_6 : prefixEval [2,1,3] lowerTau = (15/37 : ℝ) + (-1/37 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((2 : ℕ+) : ℕ) : ℝ) + prefixEval [1,3] lowerTau) = _
  rw [ar_eval_2]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((2 : ℝ) + (1/2 : ℝ)) (1/6 : ℝ)
      (15/37 : ℝ) (-1/37 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_7 : prefixEval [1,2,1,3] lowerTau = (52/73 : ℝ) + (1/73 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((1 : ℕ+) : ℕ) : ℝ) + prefixEval [2,1,3] lowerTau) = _
  rw [ar_eval_6]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((1 : ℝ) + (15/37 : ℝ)) (-1/37 : ℝ)
      (52/73 : ℝ) (1/73 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_8 : prefixEval [3,2,1,3] lowerTau = (42/143 : ℝ) + (1/429 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((3 : ℕ+) : ℕ) : ℝ) + prefixEval [2,1,3] lowerTau) = _
  rw [ar_eval_6]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((3 : ℝ) + (15/37 : ℝ)) (-1/37 : ℝ)
      (42/143 : ℝ) (1/429 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_9 : prefixEval [1,1,2,1,3] lowerTau = (125/214 : ℝ) + (-1/214 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((1 : ℕ+) : ℕ) : ℝ) + prefixEval [1,2,1,3] lowerTau) = _
  rw [ar_eval_7]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((1 : ℝ) + (52/73 : ℝ)) (1/73 : ℝ)
      (125/214 : ℝ) (-1/214 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_10 : prefixEval [2,1,2,1,3] lowerTau = (66/179 : ℝ) + (-1/537 : ℝ) * Real.sqrt 3 := by
  change 1 / ((((2 : ℕ+) : ℕ) : ℝ) + prefixEval [1,2,1,3] lowerTau) = _
  rw [ar_eval_7]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 3 ((2 : ℝ) + (52/73 : ℝ)) (1/73 : ℝ)
      (66/179 : ℝ) (-1/537 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_11 : prefixEval [] lowerAlpha = (-1/2 : ℝ) + (1/6 : ℝ) * Real.sqrt 21 := by
  dsimp [prefixEval, lowerAlpha]
  ring

private theorem ar_eval_12 : prefixEval [3] lowerAlpha = (15/34 : ℝ) + (-1/34 : ℝ) * Real.sqrt 21 := by
  change 1 / ((((3 : ℕ+) : ℕ) : ℝ) + prefixEval [] lowerAlpha) = _
  rw [ar_eval_11]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 21 ((3 : ℝ) + (-1/2 : ℝ)) (1/6 : ℝ)
      (15/34 : ℝ) (-1/34 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_13 : prefixEval [1,3] lowerAlpha = (7/10 : ℝ) + (1/70 : ℝ) * Real.sqrt 21 := by
  change 1 / ((((1 : ℕ+) : ℕ) : ℝ) + prefixEval [3] lowerAlpha) = _
  rw [ar_eval_12]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 21 ((1 : ℝ) + (15/34 : ℝ)) (-1/34 : ℝ)
      (7/10 : ℝ) (1/70 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_14 : prefixEval [3,3] lowerAlpha = (39/134 : ℝ) + (1/402 : ℝ) * Real.sqrt 21 := by
  change 1 / ((((3 : ℕ+) : ℕ) : ℝ) + prefixEval [3] lowerAlpha) = _
  rw [ar_eval_12]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 21 ((3 : ℝ) + (15/34 : ℝ)) (-1/34 : ℝ)
      (39/134 : ℝ) (1/402 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_15 : prefixEval [1,1,3] lowerAlpha = (119/202 : ℝ) + (-1/202 : ℝ) * Real.sqrt 21 := by
  change 1 / ((((1 : ℕ+) : ℕ) : ℝ) + prefixEval [1,3] lowerAlpha) = _
  rw [ar_eval_13]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 21 ((1 : ℝ) + (7/10 : ℝ)) (1/70 : ℝ)
      (119/202 : ℝ) (-1/202 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_16 : prefixEval [] lowerBeta = (-3/2 : ℝ) + (1/2 : ℝ) * Real.sqrt 21 := by
  dsimp [prefixEval, lowerBeta]
  ring

private theorem ar_eval_17 : prefixEval [1] lowerBeta = (1/10 : ℝ) + (1/10 : ℝ) * Real.sqrt 21 := by
  change 1 / ((((1 : ℕ+) : ℕ) : ℝ) + prefixEval [] lowerBeta) = _
  rw [ar_eval_16]
  simpa only [one_div, add_assoc, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat] using
    (ar_surd_inverse 21 ((1 : ℝ) + (-3/2 : ℝ)) (1/2 : ℝ)
      (1/10 : ℝ) (1/10 : ℝ) (by norm_num) (by norm_num) (by norm_num))

private theorem ar_eval_18 : prefixEval [] (lowerTau / 2) = (-1/2 : ℝ) + (1/2 : ℝ) * Real.sqrt 3 := by
  dsimp [prefixEval, lowerTau]
  ring

private theorem ar_source_3 : certFieldVal (lowerHistoryTheta 3) = (2/1 : ℝ) + (-1/1 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_20 : certFieldVal (lowerHistoryTheta 20) = (42/143 : ℝ) + (1/429 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_22 : certFieldVal (lowerHistoryTheta 22) = (39/134 : ℝ) + (1/402 : ℝ) * Real.sqrt 21 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_25 : certFieldVal (lowerHistoryTheta 25) = (5/22 : ℝ) + (1/22 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_28 : certFieldVal (lowerHistoryTheta 28) = (15/34 : ℝ) + (-1/34 : ℝ) * Real.sqrt 21 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_35 : certFieldVal (lowerHistoryTheta 35) = (66/179 : ℝ) + (-1/537 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_36 : certFieldVal (lowerHistoryTheta 36) = (-1/2 : ℝ) + (1/2 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_63 : certFieldVal (lowerHistoryTheta 63) = (4/13 : ℝ) + (1/13 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_65 : certFieldVal (lowerHistoryTheta 65) = (1/10 : ℝ) + (1/10 : ℝ) * Real.sqrt 21 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_66 : certFieldVal (lowerHistoryTheta 66) = (9/13 : ℝ) + (-1/13 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_68 : certFieldVal (lowerHistoryTheta 68) = (119/202 : ℝ) + (-1/202 : ℝ) * Real.sqrt 21 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_70 : certFieldVal (lowerHistoryTheta 70) = (125/214 : ℝ) + (-1/214 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_90 : certFieldVal (lowerHistoryTheta 90) = (52/73 : ℝ) + (1/73 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

private theorem ar_source_94 : certFieldVal (lowerHistoryTheta 94) = (1/2 : ℝ) + (1/6 : ℝ) * Real.sqrt 3 := by
  norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
    lowerHistoryInv, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau,
    certFieldAdd, certFieldScale, certFieldMul, certFieldVal]

theorem solution :
    ∀ i ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ), certFieldVal (lowerHistoryTheta i) = lowerTheta i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ar_source_3]
    change _ = prefixEval [3] lowerTau
    exact ar_eval_1.symm
  · rw [ar_source_20]
    change _ = prefixEval [3,2,1,3] lowerTau
    exact ar_eval_8.symm
  · rw [ar_source_22]
    change _ = prefixEval [3,3] lowerAlpha
    exact ar_eval_14.symm
  · rw [ar_source_25]
    change _ = prefixEval [3,3] lowerTau
    exact ar_eval_4.symm
  · rw [ar_source_28]
    change _ = prefixEval [3] lowerAlpha
    exact ar_eval_12.symm
  · rw [ar_source_35]
    change _ = prefixEval [2,1,2,1,3] lowerTau
    exact ar_eval_10.symm
  · rw [ar_source_36]
    change _ = prefixEval [] (lowerTau / 2)
    exact ar_eval_18.symm
  · rw [ar_source_63]
    change _ = prefixEval [2,3] lowerTau
    exact ar_eval_3.symm
  · rw [ar_source_65]
    change _ = prefixEval [1] lowerBeta
    exact ar_eval_17.symm
  · rw [ar_source_66]
    change _ = prefixEval [1,1,3] lowerTau
    exact ar_eval_5.symm
  · rw [ar_source_68]
    change _ = prefixEval [1,1,3] lowerAlpha
    exact ar_eval_15.symm
  · rw [ar_source_70]
    change _ = prefixEval [1,1,2,1,3] lowerTau
    exact ar_eval_9.symm
  · rw [ar_source_90]
    change _ = prefixEval [1,2,1,3] lowerTau
    exact ar_eval_7.symm
  · rw [ar_source_94]
    change _ = prefixEval [1,3] lowerTau
    exact ar_eval_2.symm

#print axioms solution
