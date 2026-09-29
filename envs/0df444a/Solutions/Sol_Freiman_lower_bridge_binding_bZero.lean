-- Prove2me | solution 1 for Freiman.lower_bridge_binding_bZero
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:34:16.658297+00:00
-- url     : https://prove2.me/submissions/b4340729-2294-43c0-aea3-9f93faf480da

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

@[simp] private theorem bp_2_1 : prefixEval [2,1] lowerTau = (6 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1]
  have harg : (2 : ℝ) + ((0 : ℝ) + (1 / 3 : ℝ) * Real.sqrt 3) = (2 : ℝ) + (1 / 3 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2 : ℝ) (1 / 3 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_2 : prefixEval [2,2] lowerTau = (1 : ℝ) + (-1 / 3 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2]
  have harg : (2 : ℝ) + ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3) = (3 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_1 : prefixEval [3,1] lowerTau = (9 / 26 : ℝ) + (-1 / 26 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1]
  have harg : (3 : ℝ) + ((0 : ℝ) + (1 / 3 : ℝ) * Real.sqrt 3) = (3 : ℝ) + (1 / 3 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3 : ℝ) (1 / 3 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1 : prefixEval [1,2,1] lowerTau = (17 / 26 : ℝ) + (1 / 26 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1]
  have harg : (1 : ℝ) + ((6 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3) = (17 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (17 / 11 : ℝ) (-1 / 11 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_2 : prefixEval [1,2,2] lowerTau = (6 / 11 : ℝ) + (1 / 11 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_2]
  have harg : (1 : ℝ) + ((1 : ℝ) + (-1 / 3 : ℝ) * Real.sqrt 3) = (2 : ℝ) + (-1 / 3 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2 : ℝ) (-1 / 3 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_3 : prefixEval [1,2,3] lowerTau = (17 / 22 : ℝ) + (-1 / 22 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_3]
  have harg : (1 : ℝ) + ((4 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3) = (17 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (17 / 13 : ℝ) (1 / 13 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1 : prefixEval [1,3,1] lowerTau = (35 / 47 : ℝ) + (1 / 47 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1]
  have harg : (1 : ℝ) + ((9 / 26 : ℝ) + (-1 / 26 : ℝ) * Real.sqrt 3) = (35 / 26 : ℝ) + (-1 / 26 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (35 / 26 : ℝ) (-1 / 26 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3 : prefixEval [1,3,3] lowerTau = (9 / 11 : ℝ) + (-1 / 33 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3]
  have harg : (1 : ℝ) + ((5 / 22 : ℝ) + (1 / 22 : ℝ) * Real.sqrt 3) = (27 / 22 : ℝ) + (1 / 22 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (27 / 22 : ℝ) (1 / 22 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_2_3 : prefixEval [2,2,3] lowerTau = (10 / 23 : ℝ) + (-1 / 69 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_3]
  have harg : (2 : ℝ) + ((4 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3) = (30 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (30 / 13 : ℝ) (1 / 13 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_2_3 : prefixEval [1,2,2,3] lowerTau = (99 / 142 : ℝ) + (1 / 142 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_2_3]
  have harg : (1 : ℝ) + ((10 / 23 : ℝ) + (-1 / 69 : ℝ) * Real.sqrt 3) = (33 / 23 : ℝ) + (-1 / 69 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (33 / 23 : ℝ) (-1 / 69 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_1_3 : prefixEval [2,1,1,3] lowerTau = (35 / 94 : ℝ) + (1 / 94 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_1_3]
  have harg : (2 : ℝ) + ((9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3) = (35 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (35 / 13 : ℝ) (-1 / 13 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_2_1_3 : prefixEval [2,2,1,3] lowerTau = (89 / 214 : ℝ) + (1 / 214 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3]
  have harg : (2 : ℝ) + ((15 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3) = (89 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (89 / 37 : ℝ) (-1 / 37 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_1_3 : prefixEval [1,2,1,1,3] lowerTau = (43 / 59 : ℝ) + (-1 / 177 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_1_3]
  have harg : (1 : ℝ) + ((35 / 94 : ℝ) + (1 / 94 : ℝ) * Real.sqrt 3) = (129 / 94 : ℝ) + (1 / 94 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (129 / 94 : ℝ) (1 / 94 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_2_1_3 : prefixEval [1,2,2,1,3] lowerTau = (101 / 143 : ℝ) + (-1 / 429 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_2_1_3]
  have harg : (1 : ℝ) + ((89 / 214 : ℝ) + (1 / 214 : ℝ) * Real.sqrt 3) = (303 / 214 : ℝ) + (1 / 214 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (303 / 214 : ℝ) (1 / 214 : ℝ) (by norm_num)]
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

set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
private theorem bridge_sqrt3_cube : (Real.sqrt 3)^3 = 3 * Real.sqrt 3 := by
  calc (Real.sqrt 3)^3 = (Real.sqrt 3)^2 * Real.sqrt 3 := by ring
    _ = 3 * Real.sqrt 3 := by rw [Real.sq_sqrt (by norm_num)]

private theorem bridge_bc : LowerInitialFamily.B ≠ LowerInitialFamily.C := by intro h; cases h
private theorem bridge_ac : LowerInitialFamily.A ≠ LowerInitialFamily.C := by intro h; cases h

private theorem bridge_bZero_0 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[0]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[0]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_1 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[1]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[1]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_2 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[2]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[2]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_3 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[3]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[3]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_4 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[4]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[4]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_5 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[5]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[5]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_6 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[6]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[6]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_7 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[7]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[7]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_8 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[8]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[8]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_9 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[9]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[9]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_10 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[10]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[10]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_11 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[11]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[11]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_12 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[12]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[12]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_13 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[13]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[13]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_14 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[14]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[14]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_15 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[15]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[15]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_16 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[16]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[16]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_17 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[17]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[17]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_bZero_18 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_bZero[18]'(by decide)).polynomial x y =
      lowerBridgeNumerator .bZero (lowerBridgeRecords_bZero[18]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_bZero, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_2, bp_1_3, bp_2_1, bp_2_2, bp_2_3, bp_3_1, bp_3_3, bp_1_1_3, bp_1_2_1, bp_1_2_2, bp_1_2_3, bp_1_3_1, bp_1_3_3, bp_2_1_3, bp_2_2_3, bp_1_2_1_3, bp_1_2_2_3, bp_2_1_1_3, bp_2_2_1_3, bp_1_2_1_1_3, bp_1_2_2_1_3, bp_2_1_2_1_3, bp_3_1_2_1_3, bp_1_2_1_2_1_3, bp_1_3_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring



theorem solution : ∀ r ∈ lowerBridgeRecords .bZero, ∀ x y : ℝ,
    certPolyEval r.polynomial x y = lowerBridgeNumerator .bZero r x y := by
  intro r hr x y
  simp only [lowerBridgeRecords, lowerBridgeRecords_bZero, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bridge_bZero_0 x y
  · exact bridge_bZero_1 x y
  · exact bridge_bZero_2 x y
  · exact bridge_bZero_3 x y
  · exact bridge_bZero_4 x y
  · exact bridge_bZero_5 x y
  · exact bridge_bZero_6 x y
  · exact bridge_bZero_7 x y
  · exact bridge_bZero_8 x y
  · exact bridge_bZero_9 x y
  · exact bridge_bZero_10 x y
  · exact bridge_bZero_11 x y
  · exact bridge_bZero_12 x y
  · exact bridge_bZero_13 x y
  · exact bridge_bZero_14 x y
  · exact bridge_bZero_15 x y
  · exact bridge_bZero_16 x y
  · exact bridge_bZero_17 x y
  · exact bridge_bZero_18 x y

#print axioms solution
