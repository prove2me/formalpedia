-- Prove2me | solution 1 for Freiman.lower_bridge_binding_cPos
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:32:43.765696+00:00
-- url     : https://prove2.me/submissions/c52b6480-ca99-49a0-81e3-96902003f401

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib
open Freiman
set_option linter.unusedSimpArgs false
private theorem bridge_inv (a b : ℝ) (hd : a^2 - 3*b^2 ≠ 0) :
    1/(a+b*Real.sqrt 3) = (a-b*Real.sqrt 3)/(a^2-3*b^2) := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hm : (a+b*Real.sqrt 3)*(a-b*Real.sqrt 3) = a^2 - 3*b^2 := by
    linear_combination -b^2 * hs
  have hp : a+b*Real.sqrt 3 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hm
    exact hd hm.symm
  apply (eq_div_iff hd).2
  rw [← hm, ← mul_assoc]
  field_simp

@[simp] private theorem bp_nil : prefixEval [] lowerTau = (-1 : ℝ) + 1 * Real.sqrt 3 := by simp only [prefixEval, lowerTau]; ring

@[simp] private theorem bp_1 : prefixEval [1] lowerTau = (0 : ℝ) + (1 / 3 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_nil]
  have harg : (1 : ℝ) + ((-1 : ℝ) + (1 : ℝ) * Real.sqrt 3) = (0 : ℝ) + (1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (0 : ℝ) (1 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2 : prefixEval [2] lowerTau = (-1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_nil]
  have harg : (2 : ℝ) + ((-1 : ℝ) + (1 : ℝ) * Real.sqrt 3) = (1 : ℝ) + (1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1 : ℝ) (1 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3 : prefixEval [3] lowerTau = (2 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_nil]
  have harg : (3 : ℝ) + ((-1 : ℝ) + (1 : ℝ) * Real.sqrt 3) = (2 : ℝ) + (1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2 : ℝ) (1 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2 : prefixEval [1,2] lowerTau = (-1 : ℝ) + (1 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2]
  have harg : (1 : ℝ) + ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3) = (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3 : prefixEval [1,3] lowerTau = (1 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3]
  have harg : (1 : ℝ) + ((2 : ℝ) + (-1 : ℝ) * Real.sqrt 3) = (3 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3 : ℝ) (-1 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_3 : prefixEval [2,3] lowerTau = (4 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3]
  have harg : (2 : ℝ) + ((2 : ℝ) + (-1 : ℝ) * Real.sqrt 3) = (4 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (4 : ℝ) (-1 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3 : prefixEval [3,3] lowerTau = (5 / 22 : ℝ) + (1 / 22 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3]
  have harg : (3 : ℝ) + ((2 : ℝ) + (-1 : ℝ) * Real.sqrt 3) = (5 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5 : ℝ) (-1 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_1_3 : prefixEval [1,1,3] lowerTau = (9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3]
  have harg : (1 : ℝ) + ((1 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3) = (3 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3 / 2 : ℝ) (1 / 6 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3 : prefixEval [2,1,3] lowerTau = (15 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3]
  have harg : (2 : ℝ) + ((1 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3) = (5 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5 / 2 : ℝ) (1 / 6 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3 : prefixEval [1,2,1,3] lowerTau = (52 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3]
  have harg : (1 : ℝ) + ((15 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3) = (52 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (52 / 37 : ℝ) (-1 / 37 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_2_1_3 : prefixEval [3,2,1,3] lowerTau = (42 / 143 : ℝ) + (1 / 429 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3]
  have harg : (3 : ℝ) + ((15 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3) = (126 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (126 / 37 : ℝ) (-1 / 37 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_2_1_3 : prefixEval [2,1,2,1,3] lowerTau = (66 / 179 : ℝ) + (-1 / 537 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_3]
  have harg : (2 : ℝ) + ((52 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3) = (198 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (198 / 73 : ℝ) (1 / 73 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_1_3 : prefixEval [3,1,2,1,3] lowerTau = (271 / 1006 : ℝ) + (-1 / 1006 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_3]
  have harg : (3 : ℝ) + ((52 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3) = (271 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (271 / 73 : ℝ) (1 / 73 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_2_1_3 : prefixEval [3,3,2,1,3] lowerTau = (1413 / 4654 : ℝ) + (-1 / 4654 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_2_1_3]
  have harg : (3 : ℝ) + ((42 / 143 : ℝ) + (1 / 429 : ℝ) * Real.sqrt 3) = (471 / 143 : ℝ) + (1 / 429 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (471 / 143 : ℝ) (1 / 429 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_2_1_3 : prefixEval [1,2,1,2,1,3] lowerTau = (735 / 1006 : ℝ) + (1 / 1006 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_2_1_3]
  have harg : (1 : ℝ) + ((66 / 179 : ℝ) + (-1 / 537 : ℝ) * Real.sqrt 3) = (245 / 179 : ℝ) + (-1 / 537 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (245 / 179 : ℝ) (-1 / 537 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_1_3 : prefixEval [1,3,1,2,1,3] lowerTau = (1277 / 1621 : ℝ) + (1 / 1621 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1_3]
  have harg : (1 : ℝ) + ((271 / 1006 : ℝ) + (-1 / 1006 : ℝ) * Real.sqrt 3) = (1277 / 1006 : ℝ) + (-1 / 1006 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1277 / 1006 : ℝ) (-1 / 1006 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_1_2_1_3 : prefixEval [3,3,1,2,1,3] lowerTau = (3289 / 10753 : ℝ) + (1 / 10753 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1_3]
  have harg : (3 : ℝ) + ((271 / 1006 : ℝ) + (-1 / 1006 : ℝ) * Real.sqrt 3) = (3289 / 1006 : ℝ) + (-1 / 1006 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3289 / 1006 : ℝ) (-1 / 1006 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_2_1_3 : prefixEval [2,1,3,1,2,1,3] lowerTau = (4519 / 12598 : ℝ) + (-1 / 12598 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1_3]
  have harg : (2 : ℝ) + ((1277 / 1621 : ℝ) + (1 / 1621 : ℝ) * Real.sqrt 3) = (4519 / 1621 : ℝ) + (1 / 1621 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (4519 / 1621 : ℝ) (1 / 1621 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_1_2_1_3 : prefixEval [3,1,2,1,2,1,3] lowerTau = (1251 / 4667 : ℝ) + (-1 / 14001 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_2_1_3]
  have harg : (3 : ℝ) + ((735 / 1006 : ℝ) + (1 / 1006 : ℝ) * Real.sqrt 3) = (3753 / 1006 : ℝ) + (1 / 1006 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3753 / 1006 : ℝ) (1 / 1006 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_1_2_1_3 : prefixEval [1,3,1,2,1,2,1,3] lowerTau = (17754 / 22513 : ℝ) + (1 / 22513 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1_2_1_3]
  have harg : (1 : ℝ) + ((1251 / 4667 : ℝ) + (-1 / 14001 : ℝ) * Real.sqrt 3) = (5918 / 4667 : ℝ) + (-1 / 14001 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5918 / 4667 : ℝ) (-1 / 14001 : ℝ) (by norm_num)]
  norm_num
  ring

set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
private theorem bridge_sqrt3_cube : (Real.sqrt 3)^3 = 3 * Real.sqrt 3 := by
  calc (Real.sqrt 3)^3 = (Real.sqrt 3)^2 * Real.sqrt 3 := by ring
    _ = 3 * Real.sqrt 3 := by rw [Real.sq_sqrt (by norm_num)]

private theorem bridge_cPos_0 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_cPos[0]'(by decide)).polynomial x y =
      lowerBridgeNumerator .cPos (lowerBridgeRecords_cPos[0]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_cPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_3, bp_3_3, bp_1_1_3, bp_2_1_3, bp_1_2_1_3, bp_3_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_3_3_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3, bp_3_3_1_2_1_3, bp_2_1_3_1_2_1_3, bp_3_1_2_1_2_1_3, bp_1_3_1_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_cPos_1 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_cPos[1]'(by decide)).polynomial x y =
      lowerBridgeNumerator .cPos (lowerBridgeRecords_cPos[1]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_cPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_3, bp_3_3, bp_1_1_3, bp_2_1_3, bp_1_2_1_3, bp_3_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_3_3_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3, bp_3_3_1_2_1_3, bp_2_1_3_1_2_1_3, bp_3_1_2_1_2_1_3, bp_1_3_1_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_cPos_2 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_cPos[2]'(by decide)).polynomial x y =
      lowerBridgeNumerator .cPos (lowerBridgeRecords_cPos[2]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_cPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_3, bp_3_3, bp_1_1_3, bp_2_1_3, bp_1_2_1_3, bp_3_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_3_3_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3, bp_3_3_1_2_1_3, bp_2_1_3_1_2_1_3, bp_3_1_2_1_2_1_3, bp_1_3_1_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_cPos_3 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_cPos[3]'(by decide)).polynomial x y =
      lowerBridgeNumerator .cPos (lowerBridgeRecords_cPos[3]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_cPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_3, bp_3_3, bp_1_1_3, bp_2_1_3, bp_1_2_1_3, bp_3_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_3_3_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3, bp_3_3_1_2_1_3, bp_2_1_3_1_2_1_3, bp_3_1_2_1_2_1_3, bp_1_3_1_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_cPos_4 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_cPos[4]'(by decide)).polynomial x y =
      lowerBridgeNumerator .cPos (lowerBridgeRecords_cPos[4]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_cPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_3, bp_3_3, bp_1_1_3, bp_2_1_3, bp_1_2_1_3, bp_3_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_3_3_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3, bp_3_3_1_2_1_3, bp_2_1_3_1_2_1_3, bp_3_1_2_1_2_1_3, bp_1_3_1_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_cPos_5 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_cPos[5]'(by decide)).polynomial x y =
      lowerBridgeNumerator .cPos (lowerBridgeRecords_cPos[5]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_cPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_3, bp_3_3, bp_1_1_3, bp_2_1_3, bp_1_2_1_3, bp_3_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_3_3_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3, bp_3_3_1_2_1_3, bp_2_1_3_1_2_1_3, bp_3_1_2_1_2_1_3, bp_1_3_1_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring



theorem solution : ∀ r ∈ lowerBridgeRecords .cPos, ∀ x y : ℝ,
    certPolyEval r.polynomial x y = lowerBridgeNumerator .cPos r x y := by
  intro r hr x y
  simp only [lowerBridgeRecords, lowerBridgeRecords_cPos, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact bridge_cPos_0 x y
  · exact bridge_cPos_1 x y
  · exact bridge_cPos_2 x y
  · exact bridge_cPos_3 x y
  · exact bridge_cPos_4 x y
  · exact bridge_cPos_5 x y

#print axioms solution
