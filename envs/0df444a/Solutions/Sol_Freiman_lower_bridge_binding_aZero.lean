-- Prove2me | solution 1 for Freiman.lower_bridge_binding_aZero
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:16:26.219931+00:00
-- url     : https://prove2.me/submissions/a5d06146-a4de-4750-a5aa-e103e0c5db31

import Definitions.Def_Freiman_lowerBridgeCatalog
import Theorems.Thm_Freiman_lower_bridge_tau_values
import Mathlib.Tactic
open Freiman
set_option linter.unusedSimpArgs false

@[simp] private theorem bp_nil : prefixEval [] lowerTau = (-1 : ℝ) + 1 * Real.sqrt 3 := Freiman.lower_bridge_tau_values.1

@[simp] private theorem bp_3 : prefixEval [3] lowerTau = (2 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.1

@[simp] private theorem bp_2_3 : prefixEval [2,3] lowerTau = (4 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.1

@[simp] private theorem bp_3_3 : prefixEval [3,3] lowerTau = (5 / 22 : ℝ) + (1 / 22 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.1

@[simp] private theorem bp_1_1_3 : prefixEval [1,1,3] lowerTau = (9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3 : prefixEval [1,2,1,3] lowerTau = (52 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3 : prefixEval [1,2,1,3,3] lowerTau = (355 / 481 : ℝ) + (-1 / 481 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_2_1_3 : prefixEval [1,2,1,2,1,3] lowerTau = (735 / 1006 : ℝ) + (1 / 1006 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_2_3 : prefixEval [1,2,1,3,2,3] lowerTau = (2513 / 3421 : ℝ) + (1 / 3421 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3 : prefixEval [1,2,1,3,3,3] lowerTau = (4087 / 5566 : ℝ) + (1 / 5566 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_1_1_3 : prefixEval [1,2,1,3,1,1,3] lowerTau = (1006 / 1367 : ℝ) + (-1 / 4101 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_2_1_3 : prefixEval [1,2,1,3,2,1,3] lowerTau = (2504 / 3407 : ℝ) + (-1 / 10221 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_2_3 : prefixEval [1,2,1,3,3,2,3] lowerTau = (27413 / 37318 : ℝ) + (-1 / 37318 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_3 : prefixEval [1,2,1,3,3,3,3] lowerTau = (44368 / 60397 : ℝ) + (-1 / 60397 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_1_2_1_3 : prefixEval [1,2,1,3,1,2,1,3] lowerTau = (17117 / 23257 : ℝ) + (1 / 23257 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_1_1_3 : prefixEval [1,2,1,3,3,1,1,3] lowerTau = (33633 / 45793 : ℝ) + (1 / 45793 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_2_1_3 : prefixEval [1,2,1,3,3,2,1,3] lowerTau = (82443 / 112237 : ℝ) + (1 / 112237 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_2_3 : prefixEval [1,2,1,3,3,3,2,3] lowerTau = (299030 / 407077 : ℝ) + (1 / 407077 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_3_3 : prefixEval [1,2,1,3,3,3,3,3] lowerTau = (484195 / 659149 : ℝ) + (1 / 659149 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_1_2_1_3 : prefixEval [1,2,1,3,3,1,2,1,3] lowerTau = (190985 / 260038 : ℝ) + (-1 / 260038 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_1_1_3 : prefixEval [1,2,1,3,3,3,1,1,3] lowerTau = (122055 / 166154 : ℝ) + (-1 / 498462 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_2_1_3 : prefixEval [1,2,1,3,3,3,2,1,3] lowerTau = (299605 / 407858 : ℝ) + (-1 / 1223574 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_3_2_3 : prefixEval [1,2,1,3,3,3,3,2,3] lowerTau = (3261917 / 4440529 : ℝ) + (-1 / 4440529 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_2_1_3_1_3_2_3 : prefixEval [1,2,1,2,1,3,1,3,2,3] lowerTau = (804501 / 1098526 : ℝ) + (1 / 1098526 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_3 : prefixEval [1,2,1,3,1,3,1,2,2,3] lowerTau = (253237 / 343967 : ℝ) + (1 / 1031901 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_1_2_1_3 : prefixEval [1,2,1,3,3,3,1,2,1,3] lowerTau = (2079038 / 2830201 : ℝ) + (1 / 2830201 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_3_1_1_3 : prefixEval [1,2,1,3,3,3,3,1,1,3] lowerTau = (3994962 / 5438449 : ℝ) + (1 / 5438449 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_3_2_1_3 : prefixEval [1,2,1,3,3,3,3,2,1,3] lowerTau = (9805068 / 13347889 : ℝ) + (1 / 13347889 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_2_1_3_1_3_2_1_3 : prefixEval [1,2,1,2,1,3,1,3,2,1,3] lowerTau = (2402518 / 3280573 : ℝ) + (-1 / 3280573 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_1_3 : prefixEval [1,2,1,3,1,3,1,2,2,1,3] lowerTau = (2304533 / 3130198 : ℝ) + (-1 / 3130198 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_2_3 : prefixEval [1,2,1,3,1,3,1,2,2,2,3] lowerTau = (4377673 / 5946097 : ℝ) + (-1 / 5946097 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_3_3_3_1_2_1_3 : prefixEval [1,2,1,3,3,3,3,1,2,1,3] lowerTau = (22683113 / 30879133 : ℝ) + (-1 / 30879133 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_1_1_3 : prefixEval [1,2,1,3,1,3,1,2,2,1,1,3] lowerTau = (5735298 / 7790137 : ℝ) + (1 / 7790137 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_2_1_3 : prefixEval [1,2,1,3,1,3,1,2,2,2,1,3] lowerTau = (13419276 / 18227113 : ℝ) + (1 / 18227113 : ℝ) * Real.sqrt 3 := Freiman.lower_bridge_tau_values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
private theorem bridge_sqrt3_cube : (Real.sqrt 3)^3 = 3 * Real.sqrt 3 := by
  calc (Real.sqrt 3)^3 = (Real.sqrt 3)^2 * Real.sqrt 3 := by ring
    _ = 3 * Real.sqrt 3 := by rw [Real.sq_sqrt (by norm_num)]

private theorem bridge_bc : LowerInitialFamily.B ≠ LowerInitialFamily.C := by intro h; cases h
private theorem bridge_ac : LowerInitialFamily.A ≠ LowerInitialFamily.C := by intro h; cases h

private theorem bridge_aZero_0 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[0]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[0]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_1 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[1]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[1]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_2 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[2]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[2]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_3 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[3]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[3]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_4 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[4]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[4]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_5 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[5]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[5]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_6 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[6]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[6]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_7 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[7]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[7]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_8 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[8]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[8]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_9 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[9]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[9]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_10 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[10]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[10]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_11 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[11]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[11]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_12 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[12]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[12]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_13 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[13]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[13]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_14 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[14]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[14]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_15 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[15]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[15]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_16 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[16]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[16]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_17 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[17]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[17]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_18 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[18]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[18]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3_1_1_3, bp_1_2_1_3_3_3_3_1_2_1_3, bp_1_2_1_3_3_3_3_2_3, bp_1_2_1_3_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_19 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[19]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[19]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_20 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[20]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[20]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_21 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[21]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[21]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_22 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[22]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[22]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3_1_2_1_3, bp_1_2_1_3_3_3_3_2_1_3, bp_1_2_1_3_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_23 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[23]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[23]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_24 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[24]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[24]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_25 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[25]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[25]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_26 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[26]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[26]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_27 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[27]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[27]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_28 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[28]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[28]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_2_1_1_3, bp_1_2_1_3_1_3_1_2_2_2_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_29 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[29]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[29]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_30 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[30]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[30]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_31 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[31]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[31]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_32 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[32]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[32]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_33 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[33]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[33]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_2_1_3, bp_1_2_1_3_1_3_1_2_2_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_34 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[34]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[34]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_35 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[35]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[35]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_36 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[36]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[36]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_37 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[37]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[37]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_38 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[38]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[38]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_39 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[39]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[39]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_40 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[40]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[40]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_41 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[41]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[41]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_42 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[42]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[42]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_43 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[43]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[43]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_44 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[44]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[44]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_45 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[45]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[45]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_46 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[46]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[46]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_47 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[47]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[47]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_48 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[48]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[48]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_49 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[49]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[49]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_50 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[50]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[50]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_51 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[51]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[51]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_52 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[52]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[52]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_53 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[53]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[53]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_54 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[54]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[54]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_55 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[55]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[55]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_56 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[56]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[56]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_57 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[57]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[57]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3, bp_1_2_1_3_3_3_3_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_58 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[58]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[58]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_59 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[59]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[59]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_60 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[60]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[60]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_61 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[61]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[61]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_62 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[62]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[62]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_2_1_3, bp_1_2_1_3_3_3_3_2_1_3, bp_1_2_1_3_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_63 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[63]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[63]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_64 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[64]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[64]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_65 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[65]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[65]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_66 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[66]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[66]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_67 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[67]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[67]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_2_3, bp_1_2_1_3_3_3_2_1_3, bp_1_2_1_3_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_68 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[68]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[68]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_3_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_69 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[69]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[69]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_70 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[70]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[70]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_71 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[71]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[71]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3, bp_1_2_1_3_3_3_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_72 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[72]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[72]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aZero_73 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aZero[73]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aZero (lowerBridgeRecords_aZero[73]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1_1_3, bp_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_2_3, bp_3, bp_3_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring



theorem solution : ∀ r ∈ lowerBridgeRecords .aZero, ∀ x y : ℝ,
    certPolyEval r.polynomial x y = lowerBridgeNumerator .aZero r x y := by
  intro r hr x y
  simp only [lowerBridgeRecords, lowerBridgeRecords_aZero, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bridge_aZero_0 x y
  · exact bridge_aZero_1 x y
  · exact bridge_aZero_2 x y
  · exact bridge_aZero_3 x y
  · exact bridge_aZero_4 x y
  · exact bridge_aZero_5 x y
  · exact bridge_aZero_6 x y
  · exact bridge_aZero_7 x y
  · exact bridge_aZero_8 x y
  · exact bridge_aZero_9 x y
  · exact bridge_aZero_10 x y
  · exact bridge_aZero_11 x y
  · exact bridge_aZero_12 x y
  · exact bridge_aZero_13 x y
  · exact bridge_aZero_14 x y
  · exact bridge_aZero_15 x y
  · exact bridge_aZero_16 x y
  · exact bridge_aZero_17 x y
  · exact bridge_aZero_18 x y
  · exact bridge_aZero_19 x y
  · exact bridge_aZero_20 x y
  · exact bridge_aZero_21 x y
  · exact bridge_aZero_22 x y
  · exact bridge_aZero_23 x y
  · exact bridge_aZero_24 x y
  · exact bridge_aZero_25 x y
  · exact bridge_aZero_26 x y
  · exact bridge_aZero_27 x y
  · exact bridge_aZero_28 x y
  · exact bridge_aZero_29 x y
  · exact bridge_aZero_30 x y
  · exact bridge_aZero_31 x y
  · exact bridge_aZero_32 x y
  · exact bridge_aZero_33 x y
  · exact bridge_aZero_34 x y
  · exact bridge_aZero_35 x y
  · exact bridge_aZero_36 x y
  · exact bridge_aZero_37 x y
  · exact bridge_aZero_38 x y
  · exact bridge_aZero_39 x y
  · exact bridge_aZero_40 x y
  · exact bridge_aZero_41 x y
  · exact bridge_aZero_42 x y
  · exact bridge_aZero_43 x y
  · exact bridge_aZero_44 x y
  · exact bridge_aZero_45 x y
  · exact bridge_aZero_46 x y
  · exact bridge_aZero_47 x y
  · exact bridge_aZero_48 x y
  · exact bridge_aZero_49 x y
  · exact bridge_aZero_50 x y
  · exact bridge_aZero_51 x y
  · exact bridge_aZero_52 x y
  · exact bridge_aZero_53 x y
  · exact bridge_aZero_54 x y
  · exact bridge_aZero_55 x y
  · exact bridge_aZero_56 x y
  · exact bridge_aZero_57 x y
  · exact bridge_aZero_58 x y
  · exact bridge_aZero_59 x y
  · exact bridge_aZero_60 x y
  · exact bridge_aZero_61 x y
  · exact bridge_aZero_62 x y
  · exact bridge_aZero_63 x y
  · exact bridge_aZero_64 x y
  · exact bridge_aZero_65 x y
  · exact bridge_aZero_66 x y
  · exact bridge_aZero_67 x y
  · exact bridge_aZero_68 x y
  · exact bridge_aZero_69 x y
  · exact bridge_aZero_70 x y
  · exact bridge_aZero_71 x y
  · exact bridge_aZero_72 x y
  · exact bridge_aZero_73 x y

#print axioms solution
