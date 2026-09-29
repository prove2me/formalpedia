-- Prove2me | solution 1 for Freiman.lower_bridge_binding_aPos
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:44:23.217981+00:00
-- url     : https://prove2.me/submissions/4dcd3c57-f3f3-44f7-842e-3933bb578d24

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

@[simp] private theorem bp_1_1 : prefixEval [1,1] lowerTau = (3 / 2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1]
  have harg : (1 : ℝ) + ((0 : ℝ) + (1 / 3 : ℝ) * Real.sqrt 3) = (1 : ℝ) + (1 / 3 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1 : ℝ) (1 / 3 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_2 : prefixEval [3,2] lowerTau = (5 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2]
  have harg : (3 : ℝ) + ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3) = (5 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_1_1 : prefixEval [1,1,1] lowerTau = (5 / 11 : ℝ) + (1 / 11 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_1]
  have harg : (1 : ℝ) + ((3 / 2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 3) = (5 / 2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5 / 2 : ℝ) (-1 / 2 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_2 : prefixEval [1,3,2] lowerTau = (16 / 23 : ℝ) + (1 / 23 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_2]
  have harg : (1 : ℝ) + ((5 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3) = (16 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (16 / 11 : ℝ) (-1 / 11 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_1 : prefixEval [2,1,1] lowerTau = (7 / 23 : ℝ) + (1 / 23 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_1]
  have harg : (2 : ℝ) + ((3 / 2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 3) = (7 / 2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (7 / 2 : ℝ) (-1 / 2 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_2 : prefixEval [2,1,2] lowerTau = (-1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2]
  have harg : (2 : ℝ) + ((-1 : ℝ) + (1 : ℝ) * Real.sqrt 3) = (1 : ℝ) + (1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1 : ℝ) (1 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_2_1 : prefixEval [3,2,1] lowerTau = (13 / 46 : ℝ) + (1 / 138 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1]
  have harg : (3 : ℝ) + ((6 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3) = (39 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (39 / 11 : ℝ) (-1 / 11 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_2_3 : prefixEval [3,2,3] lowerTau = (43 / 142 : ℝ) + (-1 / 142 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_3]
  have harg : (3 : ℝ) + ((4 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3) = (43 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (43 / 13 : ℝ) (1 / 13 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_1 : prefixEval [3,3,1] lowerTau = (29 / 97 : ℝ) + (1 / 291 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1]
  have harg : (3 : ℝ) + ((9 / 26 : ℝ) + (-1 / 26 : ℝ) * Real.sqrt 3) = (87 / 26 : ℝ) + (-1 / 26 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (87 / 26 : ℝ) (-1 / 26 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_2 : prefixEval [3,3,2] lowerTau = (38 / 131 : ℝ) + (1 / 131 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_2]
  have harg : (3 : ℝ) + ((5 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3) = (38 / 11 : ℝ) + (-1 / 11 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (38 / 11 : ℝ) (-1 / 11 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_3 : prefixEval [3,3,3] lowerTau = (71 / 229 : ℝ) + (-1 / 229 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3]
  have harg : (3 : ℝ) + ((5 / 22 : ℝ) + (1 / 22 : ℝ) * Real.sqrt 3) = (71 / 22 : ℝ) + (1 / 22 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (71 / 22 : ℝ) (1 / 22 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_1_1_3 : prefixEval [1,1,1,3] lowerTau = (22 / 37 : ℝ) + (1 / 37 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_1_3]
  have harg : (1 : ℝ) + ((9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3) = (22 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (22 / 13 : ℝ) (-1 / 13 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_1 : prefixEval [1,2,1,1] lowerTau = (10 / 13 : ℝ) + (-1 / 39 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_1]
  have harg : (1 : ℝ) + ((7 / 23 : ℝ) + (1 / 23 : ℝ) * Real.sqrt 3) = (30 / 23 : ℝ) + (1 / 23 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (30 / 23 : ℝ) (1 / 23 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_2 : prefixEval [1,2,1,2] lowerTau = (-1 : ℝ) + (1 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_2]
  have harg : (1 : ℝ) + ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3) = (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_2_1 : prefixEval [1,3,2,1] lowerTau = (177 / 227 : ℝ) + (-1 / 227 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_2_1]
  have harg : (1 : ℝ) + ((13 / 46 : ℝ) + (1 / 138 : ℝ) * Real.sqrt 3) = (59 / 46 : ℝ) + (1 / 138 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (59 / 46 : ℝ) (1 / 138 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_2_3 : prefixEval [1,3,2,3] lowerTau = (185 / 241 : ℝ) + (1 / 241 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_2_3]
  have harg : (1 : ℝ) + ((43 / 142 : ℝ) + (-1 / 142 : ℝ) * Real.sqrt 3) = (185 / 142 : ℝ) + (-1 / 142 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (185 / 142 : ℝ) (-1 / 142 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_1 : prefixEval [1,3,3,1] lowerTau = (378 / 491 : ℝ) + (-1 / 491 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_1]
  have harg : (1 : ℝ) + ((29 / 97 : ℝ) + (1 / 291 : ℝ) * Real.sqrt 3) = (126 / 97 : ℝ) + (1 / 291 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (126 / 97 : ℝ) (1 / 291 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_2 : prefixEval [1,3,3,2] lowerTau = (169 / 218 : ℝ) + (-1 / 218 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_2]
  have harg : (1 : ℝ) + ((38 / 131 : ℝ) + (1 / 131 : ℝ) * Real.sqrt 3) = (169 / 131 : ℝ) + (1 / 131 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (169 / 131 : ℝ) (1 / 131 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3 : prefixEval [1,3,3,3] lowerTau = (100 / 131 : ℝ) + (1 / 393 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3]
  have harg : (1 : ℝ) + ((71 / 229 : ℝ) + (-1 / 229 : ℝ) * Real.sqrt 3) = (300 / 229 : ℝ) + (-1 / 229 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (300 / 229 : ℝ) (-1 / 229 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_1_1 : prefixEval [2,1,1,1] lowerTau = (9 / 22 : ℝ) + (-1 / 66 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_1_1]
  have harg : (2 : ℝ) + ((5 / 11 : ℝ) + (1 / 11 : ℝ) * Real.sqrt 3) = (27 / 11 : ℝ) + (1 / 11 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (27 / 11 : ℝ) (1 / 11 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_2_3 : prefixEval [2,1,2,3] lowerTau = (61 / 169 : ℝ) + (1 / 169 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_3]
  have harg : (2 : ℝ) + ((17 / 22 : ℝ) + (-1 / 22 : ℝ) * Real.sqrt 3) = (61 / 22 : ℝ) + (-1 / 22 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (61 / 22 : ℝ) (-1 / 22 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1 : prefixEval [2,1,3,1] lowerTau = (43 / 118 : ℝ) + (-1 / 354 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1]
  have harg : (2 : ℝ) + ((35 / 47 : ℝ) + (1 / 47 : ℝ) * Real.sqrt 3) = (129 / 47 : ℝ) + (1 / 47 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (129 / 47 : ℝ) (1 / 47 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_2 : prefixEval [2,1,3,2] lowerTau = (62 / 167 : ℝ) + (-1 / 167 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_2]
  have harg : (2 : ℝ) + ((16 / 23 : ℝ) + (1 / 23 : ℝ) * Real.sqrt 3) = (62 / 23 : ℝ) + (1 / 23 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (62 / 23 : ℝ) (1 / 23 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3 : prefixEval [2,1,3,3] lowerTau = (93 / 262 : ℝ) + (1 / 262 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3]
  have harg : (2 : ℝ) + ((9 / 11 : ℝ) + (-1 / 33 : ℝ) * Real.sqrt 3) = (31 / 11 : ℝ) + (-1 / 33 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (31 / 11 : ℝ) (-1 / 33 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_1_3 : prefixEval [3,1,1,3] lowerTau = (16 / 59 : ℝ) + (1 / 177 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_1_3]
  have harg : (3 : ℝ) + ((9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3) = (48 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (48 / 13 : ℝ) (-1 / 13 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_1 : prefixEval [3,1,2,1] lowerTau = (95 / 347 : ℝ) + (-1 / 347 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1]
  have harg : (3 : ℝ) + ((17 / 26 : ℝ) + (1 / 26 : ℝ) * Real.sqrt 3) = (95 / 26 : ℝ) + (1 / 26 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (95 / 26 : ℝ) (1 / 26 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_2 : prefixEval [3,1,3,2] lowerTau = (85 / 314 : ℝ) + (-1 / 314 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_2]
  have harg : (3 : ℝ) + ((16 / 23 : ℝ) + (1 / 23 : ℝ) * Real.sqrt 3) = (85 / 23 : ℝ) + (1 / 23 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (85 / 23 : ℝ) (1 / 23 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_3_2_3 : prefixEval [3,3,2,3] lowerTau = (469 / 1549 : ℝ) + (1 / 1549 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_2_3]
  have harg : (3 : ℝ) + ((43 / 142 : ℝ) + (-1 / 142 : ℝ) * Real.sqrt 3) = (469 / 142 : ℝ) + (-1 / 142 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (469 / 142 : ℝ) (-1 / 142 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_3_1 : prefixEval [3,3,3,1] lowerTau = (960 / 3167 : ℝ) + (-1 / 3167 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_1]
  have harg : (3 : ℝ) + ((29 / 97 : ℝ) + (1 / 291 : ℝ) * Real.sqrt 3) = (320 / 97 : ℝ) + (1 / 291 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (320 / 97 : ℝ) (1 / 291 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_3_2 : prefixEval [3,3,3,2] lowerTau = (431 / 1418 : ℝ) + (-1 / 1418 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_2]
  have harg : (3 : ℝ) + ((38 / 131 : ℝ) + (1 / 131 : ℝ) * Real.sqrt 3) = (431 / 131 : ℝ) + (1 / 131 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (431 / 131 : ℝ) (1 / 131 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_3_3 : prefixEval [3,3,3,3] lowerTau = (758 / 2509 : ℝ) + (1 / 2509 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3]
  have harg : (3 : ℝ) + ((71 / 229 : ℝ) + (-1 / 229 : ℝ) * Real.sqrt 3) = (758 / 229 : ℝ) + (-1 / 229 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (758 / 229 : ℝ) (-1 / 229 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_1_1 : prefixEval [1,2,1,1,1] lowerTau = (93 / 131 : ℝ) + (1 / 131 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_1_1]
  have harg : (1 : ℝ) + ((9 / 22 : ℝ) + (-1 / 66 : ℝ) * Real.sqrt 3) = (31 / 22 : ℝ) + (-1 / 66 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (31 / 22 : ℝ) (-1 / 66 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1_2_3 : prefixEval [1,2,1,2,3] lowerTau = (230 / 313 : ℝ) + (-1 / 313 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_2_3]
  have harg : (1 : ℝ) + ((61 / 169 : ℝ) + (1 / 169 : ℝ) * Real.sqrt 3) = (230 / 169 : ℝ) + (1 / 169 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (230 / 169 : ℝ) (1 / 169 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1 : prefixEval [1,2,1,3,1] lowerTau = (483 / 659 : ℝ) + (1 / 659 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1]
  have harg : (1 : ℝ) + ((43 / 118 : ℝ) + (-1 / 354 : ℝ) * Real.sqrt 3) = (161 / 118 : ℝ) + (-1 / 354 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (161 / 118 : ℝ) (-1 / 354 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_2 : prefixEval [1,2,1,3,2] lowerTau = (229 / 314 : ℝ) + (1 / 314 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_2]
  have harg : (1 : ℝ) + ((62 / 167 : ℝ) + (-1 / 167 : ℝ) * Real.sqrt 3) = (229 / 167 : ℝ) + (-1 / 167 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (229 / 167 : ℝ) (-1 / 167 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3 : prefixEval [1,2,1,3,3] lowerTau = (355 / 481 : ℝ) + (-1 / 481 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3]
  have harg : (1 : ℝ) + ((93 / 262 : ℝ) + (1 / 262 : ℝ) * Real.sqrt 3) = (355 / 262 : ℝ) + (1 / 262 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (355 / 262 : ℝ) (1 / 262 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_1_3 : prefixEval [1,3,1,1,3] lowerTau = (225 / 286 : ℝ) + (-1 / 286 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_1_3]
  have harg : (1 : ℝ) + ((16 / 59 : ℝ) + (1 / 177 : ℝ) * Real.sqrt 3) = (75 / 59 : ℝ) + (1 / 177 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (75 / 59 : ℝ) (1 / 177 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_1 : prefixEval [1,3,1,2,1] lowerTau = (442 / 563 : ℝ) + (1 / 563 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1]
  have harg : (1 : ℝ) + ((95 / 347 : ℝ) + (-1 / 347 : ℝ) * Real.sqrt 3) = (442 / 347 : ℝ) + (-1 / 347 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (442 / 347 : ℝ) (-1 / 347 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_2 : prefixEval [1,3,1,3,2] lowerTau = (133 / 169 : ℝ) + (1 / 507 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_2]
  have harg : (1 : ℝ) + ((85 / 314 : ℝ) + (-1 / 314 : ℝ) * Real.sqrt 3) = (399 / 314 : ℝ) + (-1 / 314 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (399 / 314 : ℝ) (-1 / 314 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_2_1_3 : prefixEval [1,3,2,1,3] lowerTau = (555 / 718 : ℝ) + (-1 / 718 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_2_1_3]
  have harg : (1 : ℝ) + ((42 / 143 : ℝ) + (1 / 429 : ℝ) * Real.sqrt 3) = (185 / 143 : ℝ) + (1 / 429 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (185 / 143 : ℝ) (1 / 429 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_2_3 : prefixEval [1,3,3,2,3] lowerTau = (2018 / 2629 : ℝ) + (-1 / 2629 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_2_3]
  have harg : (1 : ℝ) + ((469 / 1549 : ℝ) + (1 / 1549 : ℝ) * Real.sqrt 3) = (2018 / 1549 : ℝ) + (1 / 1549 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2018 / 1549 : ℝ) (1 / 1549 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3_1 : prefixEval [1,3,3,3,1] lowerTau = (4127 / 5378 : ℝ) + (1 / 5378 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_1]
  have harg : (1 : ℝ) + ((960 / 3167 : ℝ) + (-1 / 3167 : ℝ) * Real.sqrt 3) = (4127 / 3167 : ℝ) + (-1 / 3167 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (4127 / 3167 : ℝ) (-1 / 3167 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3_2 : prefixEval [1,3,3,3,2] lowerTau = (1849 / 2411 : ℝ) + (1 / 2411 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_2]
  have harg : (1 : ℝ) + ((431 / 1418 : ℝ) + (-1 / 1418 : ℝ) * Real.sqrt 3) = (1849 / 1418 : ℝ) + (-1 / 1418 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1849 / 1418 : ℝ) (-1 / 1418 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3_3 : prefixEval [1,3,3,3,3] lowerTau = (1089 / 1418 : ℝ) + (-1 / 4254 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_3]
  have harg : (1 : ℝ) + ((758 / 2509 : ℝ) + (1 / 2509 : ℝ) * Real.sqrt 3) = (3267 / 2509 : ℝ) + (1 / 2509 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3267 / 2509 : ℝ) (1 / 2509 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_1_1_3 : prefixEval [2,1,1,1,3] lowerTau = (32 / 83 : ℝ) + (-1 / 249 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_1_1_3]
  have harg : (2 : ℝ) + ((22 / 37 : ℝ) + (1 / 37 : ℝ) * Real.sqrt 3) = (96 / 37 : ℝ) + (1 / 37 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (96 / 37 : ℝ) (1 / 37 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_3_2_3 : prefixEval [2,1,3,2,3] lowerTau = (667 / 1846 : ℝ) + (-1 / 1846 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_2_3]
  have harg : (2 : ℝ) + ((185 / 241 : ℝ) + (1 / 241 : ℝ) * Real.sqrt 3) = (667 / 241 : ℝ) + (1 / 241 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (667 / 241 : ℝ) (1 / 241 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_1 : prefixEval [2,1,3,3,1] lowerTau = (1360 / 3767 : ℝ) + (1 / 3767 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_1]
  have harg : (2 : ℝ) + ((378 / 491 : ℝ) + (-1 / 491 : ℝ) * Real.sqrt 3) = (1360 / 491 : ℝ) + (-1 / 491 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1360 / 491 : ℝ) (-1 / 491 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_2 : prefixEval [2,1,3,3,2] lowerTau = (605 / 1679 : ℝ) + (1 / 1679 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_2]
  have harg : (2 : ℝ) + ((169 / 218 : ℝ) + (-1 / 218 : ℝ) * Real.sqrt 3) = (605 / 218 : ℝ) + (-1 / 218 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (605 / 218 : ℝ) (-1 / 218 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3 : prefixEval [2,1,3,3,3] lowerTau = (1086 / 3001 : ℝ) + (-1 / 3001 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3]
  have harg : (2 : ℝ) + ((100 / 131 : ℝ) + (1 / 393 : ℝ) * Real.sqrt 3) = (362 / 131 : ℝ) + (1 / 393 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (362 / 131 : ℝ) (1 / 393 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_1_1 : prefixEval [3,1,2,1,1] lowerTau = (147 / 554 : ℝ) + (1 / 554 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_1]
  have harg : (3 : ℝ) + ((10 / 13 : ℝ) + (-1 / 39 : ℝ) * Real.sqrt 3) = (49 / 13 : ℝ) + (-1 / 39 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (49 / 13 : ℝ) (-1 / 39 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_1_2 : prefixEval [3,1,2,1,2] lowerTau = (2 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_2]
  have harg : (3 : ℝ) + ((-1 : ℝ) + (1 : ℝ) * Real.sqrt 3) = (2 : ℝ) + (1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2 : ℝ) (1 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_1_3_2_1 : prefixEval [3,1,3,2,1] lowerTau = (286 / 1081 : ℝ) + (1 / 3243 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_2_1]
  have harg : (3 : ℝ) + ((177 / 227 : ℝ) + (-1 / 227 : ℝ) * Real.sqrt 3) = (858 / 227 : ℝ) + (-1 / 227 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (858 / 227 : ℝ) (-1 / 227 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_2_3 : prefixEval [3,1,3,2,3] lowerTau = (908 / 3421 : ℝ) + (-1 / 3421 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_2_3]
  have harg : (3 : ℝ) + ((185 / 241 : ℝ) + (1 / 241 : ℝ) * Real.sqrt 3) = (908 / 241 : ℝ) + (1 / 241 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (908 / 241 : ℝ) (1 / 241 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_1_1_3 : prefixEval [3,3,1,1,3] lowerTau = (579 / 1894 : ℝ) + (-1 / 1894 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_1_3]
  have harg : (3 : ℝ) + ((16 / 59 : ℝ) + (1 / 177 : ℝ) * Real.sqrt 3) = (193 / 59 : ℝ) + (1 / 177 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (193 / 59 : ℝ) (1 / 177 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_3_3_2_3 : prefixEval [3,3,3,2,3] lowerTau = (5116 / 16897 : ℝ) + (-1 / 16897 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_2_3]
  have harg : (3 : ℝ) + ((469 / 1549 : ℝ) + (1 / 1549 : ℝ) * Real.sqrt 3) = (5116 / 1549 : ℝ) + (1 / 1549 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5116 / 1549 : ℝ) (1 / 1549 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_1_1_3 : prefixEval [1,2,1,1,1,3] lowerTau = (345 / 478 : ℝ) + (1 / 478 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_1_1_3]
  have harg : (1 : ℝ) + ((32 / 83 : ℝ) + (-1 / 249 : ℝ) * Real.sqrt 3) = (115 / 83 : ℝ) + (-1 / 249 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (115 / 83 : ℝ) (-1 / 249 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1_3_2_3 : prefixEval [1,2,1,3,2,3] lowerTau = (2513 / 3421 : ℝ) + (1 / 3421 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_2_3]
  have harg : (1 : ℝ) + ((667 / 1846 : ℝ) + (-1 / 1846 : ℝ) * Real.sqrt 3) = (2513 / 1846 : ℝ) + (-1 / 1846 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2513 / 1846 : ℝ) (-1 / 1846 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_1 : prefixEval [1,2,1,3,3,1] lowerTau = (1709 / 2326 : ℝ) + (-1 / 6978 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_1]
  have harg : (1 : ℝ) + ((1360 / 3767 : ℝ) + (1 / 3767 : ℝ) * Real.sqrt 3) = (5127 / 3767 : ℝ) + (1 / 3767 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5127 / 3767 : ℝ) (1 / 3767 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_2 : prefixEval [1,2,1,3,3,2] lowerTau = (2284 / 3107 : ℝ) + (-1 / 3107 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_2]
  have harg : (1 : ℝ) + ((605 / 1679 : ℝ) + (1 / 1679 : ℝ) * Real.sqrt 3) = (2284 / 1679 : ℝ) + (1 / 1679 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2284 / 1679 : ℝ) (1 / 1679 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3 : prefixEval [1,2,1,3,3,3] lowerTau = (4087 / 5566 : ℝ) + (1 / 5566 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3]
  have harg : (1 : ℝ) + ((1086 / 3001 : ℝ) + (-1 / 3001 : ℝ) * Real.sqrt 3) = (4087 / 3001 : ℝ) + (-1 / 3001 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (4087 / 3001 : ℝ) (-1 / 3001 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_1_1 : prefixEval [1,3,1,2,1,1] lowerTau = (701 / 887 : ℝ) + (-1 / 887 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1_1]
  have harg : (1 : ℝ) + ((147 / 554 : ℝ) + (1 / 554 : ℝ) * Real.sqrt 3) = (701 / 554 : ℝ) + (1 / 554 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (701 / 554 : ℝ) (1 / 554 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_1_2 : prefixEval [1,3,1,2,1,2] lowerTau = (1 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1_2]
  have harg : (1 : ℝ) + ((2 : ℝ) + (-1 : ℝ) * Real.sqrt 3) = (3 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3 : ℝ) (-1 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_1_3_2_1 : prefixEval [1,3,1,3,2,1] lowerTau = (4101 / 5186 : ℝ) + (-1 / 5186 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_2_1]
  have harg : (1 : ℝ) + ((286 / 1081 : ℝ) + (1 / 3243 : ℝ) * Real.sqrt 3) = (1367 / 1081 : ℝ) + (1 / 3243 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1367 / 1081 : ℝ) (1 / 3243 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_2_3 : prefixEval [1,3,1,3,2,3] lowerTau = (1443 / 1826 : ℝ) + (1 / 5478 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_2_3]
  have harg : (1 : ℝ) + ((908 / 3421 : ℝ) + (-1 / 3421 : ℝ) * Real.sqrt 3) = (4329 / 3421 : ℝ) + (-1 / 3421 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (4329 / 3421 : ℝ) (-1 / 3421 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_1_1_3 : prefixEval [1,3,3,1,1,3] lowerTau = (2473 / 3229 : ℝ) + (1 / 3229 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_1_1_3]
  have harg : (1 : ℝ) + ((579 / 1894 : ℝ) + (-1 / 1894 : ℝ) * Real.sqrt 3) = (2473 / 1894 : ℝ) + (-1 / 1894 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2473 / 1894 : ℝ) (-1 / 1894 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_2_1_3 : prefixEval [1,3,3,2,1,3] lowerTau = (6067 / 7909 : ℝ) + (1 / 7909 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_2_1_3]
  have harg : (1 : ℝ) + ((1413 / 4654 : ℝ) + (-1 / 4654 : ℝ) * Real.sqrt 3) = (6067 / 4654 : ℝ) + (-1 / 4654 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (6067 / 4654 : ℝ) (-1 / 4654 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3_2_3 : prefixEval [1,3,3,3,2,3] lowerTau = (22013 / 28678 : ℝ) + (1 / 28678 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_2_3]
  have harg : (1 : ℝ) + ((5116 / 16897 : ℝ) + (-1 / 16897 : ℝ) * Real.sqrt 3) = (22013 / 16897 : ℝ) + (-1 / 16897 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (22013 / 16897 : ℝ) (-1 / 16897 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_1_3 : prefixEval [2,1,3,1,1,3] lowerTau = (797 / 2221 : ℝ) + (1 / 2221 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_1_3]
  have harg : (2 : ℝ) + ((225 / 286 : ℝ) + (-1 / 286 : ℝ) * Real.sqrt 3) = (797 / 286 : ℝ) + (-1 / 286 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (797 / 286 : ℝ) (-1 / 286 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_2 : prefixEval [2,1,3,1,3,2] lowerTau = (1413 / 3938 : ℝ) + (-1 / 3938 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_2]
  have harg : (2 : ℝ) + ((133 / 169 : ℝ) + (1 / 507 : ℝ) * Real.sqrt 3) = (471 / 169 : ℝ) + (1 / 507 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (471 / 169 : ℝ) (1 / 507 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_2_1_3 : prefixEval [2,1,3,2,1,3] lowerTau = (1991 / 5521 : ℝ) + (1 / 5521 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_2_1_3]
  have harg : (2 : ℝ) + ((555 / 718 : ℝ) + (-1 / 718 : ℝ) * Real.sqrt 3) = (1991 / 718 : ℝ) + (-1 / 718 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1991 / 718 : ℝ) (-1 / 718 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_2_3 : prefixEval [2,1,3,3,2,3] lowerTau = (7276 / 20137 : ℝ) + (1 / 20137 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_2_3]
  have harg : (2 : ℝ) + ((2018 / 2629 : ℝ) + (-1 / 2629 : ℝ) * Real.sqrt 3) = (7276 / 2629 : ℝ) + (-1 / 2629 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (7276 / 2629 : ℝ) (-1 / 2629 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3_1 : prefixEval [2,1,3,3,3,1] lowerTau = (4961 / 13729 : ℝ) + (-1 / 41187 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_1]
  have harg : (2 : ℝ) + ((4127 / 5378 : ℝ) + (1 / 5378 : ℝ) * Real.sqrt 3) = (14883 / 5378 : ℝ) + (1 / 5378 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (14883 / 5378 : ℝ) (1 / 5378 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3_2 : prefixEval [2,1,3,3,3,2] lowerTau = (6671 / 18458 : ℝ) + (-1 / 18458 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_2]
  have harg : (2 : ℝ) + ((1849 / 2411 : ℝ) + (1 / 2411 : ℝ) * Real.sqrt 3) = (6671 / 2411 : ℝ) + (1 / 2411 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (6671 / 2411 : ℝ) (1 / 2411 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3_3 : prefixEval [2,1,3,3,3,3] lowerTau = (11775 / 32593 : ℝ) + (1 / 32593 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_3]
  have harg : (2 : ℝ) + ((1089 / 1418 : ℝ) + (-1 / 4254 : ℝ) * Real.sqrt 3) = (3925 / 1418 : ℝ) + (-1 / 4254 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3925 / 1418 : ℝ) (-1 / 4254 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_1_1_1 : prefixEval [3,1,2,1,1,1] lowerTau = (162 / 601 : ℝ) + (-1 / 1803 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_1_1]
  have harg : (3 : ℝ) + ((93 / 131 : ℝ) + (1 / 131 : ℝ) * Real.sqrt 3) = (486 / 131 : ℝ) + (1 / 131 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (486 / 131 : ℝ) (1 / 131 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_1_1_3 : prefixEval [3,1,2,1,1,3] lowerTau = (660 / 2461 : ℝ) + (1 / 2461 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_1_3]
  have harg : (3 : ℝ) + ((43 / 59 : ℝ) + (-1 / 177 : ℝ) * Real.sqrt 3) = (220 / 59 : ℝ) + (-1 / 177 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (220 / 59 : ℝ) (-1 / 177 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_1_2_3 : prefixEval [3,1,2,1,2,3] lowerTau = (1169 / 4366 : ℝ) + (1 / 4366 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_2_3]
  have harg : (3 : ℝ) + ((230 / 313 : ℝ) + (-1 / 313 : ℝ) * Real.sqrt 3) = (1169 / 313 : ℝ) + (-1 / 313 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1169 / 313 : ℝ) (-1 / 313 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_1 : prefixEval [3,1,3,1,2,1] lowerTau = (2131 / 8066 : ℝ) + (-1 / 8066 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1]
  have harg : (3 : ℝ) + ((442 / 563 : ℝ) + (1 / 563 : ℝ) * Real.sqrt 3) = (2131 / 563 : ℝ) + (1 / 563 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2131 / 563 : ℝ) (1 / 563 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_2_1_3 : prefixEval [3,1,3,2,1,3] lowerTau = (903 / 3407 : ℝ) + (1 / 10221 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_2_1_3]
  have harg : (3 : ℝ) + ((555 / 718 : ℝ) + (-1 / 718 : ℝ) * Real.sqrt 3) = (2709 / 718 : ℝ) + (-1 / 718 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2709 / 718 : ℝ) (-1 / 718 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_2_1_2_1_3 : prefixEval [3,2,1,2,1,3] lowerTau = (1809 / 6094 : ℝ) + (1 / 6094 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_2_1_3]
  have harg : (3 : ℝ) + ((66 / 179 : ℝ) + (-1 / 537 : ℝ) * Real.sqrt 3) = (603 / 179 : ℝ) + (-1 / 537 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (603 / 179 : ℝ) (-1 / 537 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_3_3_1_1_3 : prefixEval [3,3,3,1,1,3] lowerTau = (2087 / 6899 : ℝ) + (1 / 20697 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_1_1_3]
  have harg : (3 : ℝ) + ((579 / 1894 : ℝ) + (-1 / 1894 : ℝ) * Real.sqrt 3) = (6261 / 1894 : ℝ) + (-1 / 1894 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (6261 / 1894 : ℝ) (-1 / 1894 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_3_2_1_3 : prefixEval [3,3,3,2,1,3] lowerTau = (5125 / 16931 : ℝ) + (1 / 50793 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_2_1_3]
  have harg : (3 : ℝ) + ((1413 / 4654 : ℝ) + (-1 / 4654 : ℝ) * Real.sqrt 3) = (15375 / 4654 : ℝ) + (-1 / 4654 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (15375 / 4654 : ℝ) (-1 / 4654 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_1_3 : prefixEval [1,2,1,3,1,1,3] lowerTau = (1006 / 1367 : ℝ) + (-1 / 4101 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_1_3]
  have harg : (1 : ℝ) + ((797 / 2221 : ℝ) + (1 / 2221 : ℝ) * Real.sqrt 3) = (3018 / 2221 : ℝ) + (1 / 2221 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3018 / 2221 : ℝ) (1 / 2221 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_2 : prefixEval [1,2,1,3,1,3,2] lowerTau = (5351 / 7271 : ℝ) + (1 / 7271 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_2]
  have harg : (1 : ℝ) + ((1413 / 3938 : ℝ) + (-1 / 3938 : ℝ) * Real.sqrt 3) = (5351 / 3938 : ℝ) + (-1 / 3938 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5351 / 3938 : ℝ) (-1 / 3938 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_2_1_3 : prefixEval [1,2,1,3,2,1,3] lowerTau = (2504 / 3407 : ℝ) + (-1 / 10221 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_2_1_3]
  have harg : (1 : ℝ) + ((1991 / 5521 : ℝ) + (1 / 5521 : ℝ) * Real.sqrt 3) = (7512 / 5521 : ℝ) + (1 / 5521 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (7512 / 5521 : ℝ) (1 / 5521 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_2_3 : prefixEval [1,2,1,3,3,2,3] lowerTau = (27413 / 37318 : ℝ) + (-1 / 37318 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_2_3]
  have harg : (1 : ℝ) + ((7276 / 20137 : ℝ) + (1 / 20137 : ℝ) * Real.sqrt 3) = (27413 / 20137 : ℝ) + (1 / 20137 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (27413 / 20137 : ℝ) (1 / 20137 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3_1 : prefixEval [1,2,1,3,3,3,1] lowerTau = (56070 / 76331 : ℝ) + (1 / 76331 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_1]
  have harg : (1 : ℝ) + ((4961 / 13729 : ℝ) + (-1 / 41187 : ℝ) * Real.sqrt 3) = (18690 / 13729 : ℝ) + (-1 / 41187 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (18690 / 13729 : ℝ) (-1 / 41187 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3_2 : prefixEval [1,2,1,3,3,3,2] lowerTau = (25129 / 34211 : ℝ) + (1 / 34211 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_2]
  have harg : (1 : ℝ) + ((6671 / 18458 : ℝ) + (-1 / 18458 : ℝ) * Real.sqrt 3) = (25129 / 18458 : ℝ) + (-1 / 18458 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (25129 / 18458 : ℝ) (-1 / 18458 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3_3 : prefixEval [1,2,1,3,3,3,3] lowerTau = (44368 / 60397 : ℝ) + (-1 / 60397 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_3]
  have harg : (1 : ℝ) + ((11775 / 32593 : ℝ) + (1 / 32593 : ℝ) * Real.sqrt 3) = (44368 / 32593 : ℝ) + (1 / 32593 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (44368 / 32593 : ℝ) (1 / 32593 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_1_1_1 : prefixEval [1,3,1,2,1,1,1] lowerTau = (2289 / 2906 : ℝ) + (1 / 2906 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1_1_1]
  have harg : (1 : ℝ) + ((162 / 601 : ℝ) + (-1 / 1803 : ℝ) * Real.sqrt 3) = (763 / 601 : ℝ) + (-1 / 1803 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (763 / 601 : ℝ) (-1 / 1803 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_1_1_3 : prefixEval [1,3,1,2,1,1,3] lowerTau = (3121 / 3958 : ℝ) + (-1 / 3958 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1_1_3]
  have harg : (1 : ℝ) + ((660 / 2461 : ℝ) + (1 / 2461 : ℝ) * Real.sqrt 3) = (3121 / 2461 : ℝ) + (1 / 2461 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3121 / 2461 : ℝ) (1 / 2461 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_1_2_3 : prefixEval [1,3,1,2,1,2,3] lowerTau = (1845 / 2339 : ℝ) + (-1 / 7017 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1_2_3]
  have harg : (1 : ℝ) + ((1169 / 4366 : ℝ) + (1 / 4366 : ℝ) * Real.sqrt 3) = (5535 / 4366 : ℝ) + (1 / 4366 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5535 / 4366 : ℝ) (1 / 4366 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_1 : prefixEval [1,3,1,3,1,2,1] lowerTau = (3399 / 4297 : ℝ) + (1 / 12891 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_1]
  have harg : (1 : ℝ) + ((2131 / 8066 : ℝ) + (-1 / 8066 : ℝ) * Real.sqrt 3) = (10197 / 8066 : ℝ) + (-1 / 8066 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (10197 / 8066 : ℝ) (-1 / 8066 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_2_1_3 : prefixEval [1,3,1,3,2,1,3] lowerTau = (12930 / 16357 : ℝ) + (-1 / 16357 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_2_1_3]
  have harg : (1 : ℝ) + ((903 / 3407 : ℝ) + (1 / 10221 : ℝ) * Real.sqrt 3) = (4310 / 3407 : ℝ) + (1 / 10221 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (4310 / 3407 : ℝ) (1 / 10221 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_2_1_2_1_3 : prefixEval [1,3,2,1,2,1,3] lowerTau = (7903 / 10249 : ℝ) + (-1 / 10249 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_2_1_2_1_3]
  have harg : (1 : ℝ) + ((1809 / 6094 : ℝ) + (1 / 6094 : ℝ) * Real.sqrt 3) = (7903 / 6094 : ℝ) + (1 / 6094 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (7903 / 6094 : ℝ) (1 / 6094 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_1_2_1_3 : prefixEval [1,3,3,1,2,1,3] lowerTau = (14042 / 18337 : ℝ) + (-1 / 18337 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_1_2_1_3]
  have harg : (1 : ℝ) + ((3289 / 10753 : ℝ) + (1 / 10753 : ℝ) * Real.sqrt 3) = (14042 / 10753 : ℝ) + (1 / 10753 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (14042 / 10753 : ℝ) (1 / 10753 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3_1_1_3 : prefixEval [1,3,3,3,1,1,3] lowerTau = (26958 / 35113 : ℝ) + (-1 / 35113 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_1_1_3]
  have harg : (1 : ℝ) + ((2087 / 6899 : ℝ) + (1 / 20697 : ℝ) * Real.sqrt 3) = (8986 / 6899 : ℝ) + (1 / 20697 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (8986 / 6899 : ℝ) (1 / 20697 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3_2_1_3 : prefixEval [1,3,3,3,2,1,3] lowerTau = (66168 / 86197 : ℝ) + (-1 / 86197 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_2_1_3]
  have harg : (1 : ℝ) + ((5125 / 16931 : ℝ) + (1 / 50793 : ℝ) * Real.sqrt 3) = (22056 / 16931 : ℝ) + (1 / 50793 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (22056 / 16931 : ℝ) (1 / 50793 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_3_1_3_2_1 : prefixEval [2,1,3,1,3,2,1] lowerTau = (14473 / 40391 : ℝ) + (1 / 40391 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_2_1]
  have harg : (2 : ℝ) + ((4101 / 5186 : ℝ) + (-1 / 5186 : ℝ) * Real.sqrt 3) = (14473 / 5186 : ℝ) + (-1 / 5186 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (14473 / 5186 : ℝ) (-1 / 5186 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_2_3 : prefixEval [2,1,3,1,3,2,3] lowerTau = (15285 / 42649 : ℝ) + (-1 / 42649 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_2_3]
  have harg : (2 : ℝ) + ((1443 / 1826 : ℝ) + (1 / 5478 : ℝ) * Real.sqrt 3) = (5095 / 1826 : ℝ) + (1 / 5478 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5095 / 1826 : ℝ) (1 / 5478 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_1_1_3 : prefixEval [2,1,3,3,1,1,3] lowerTau = (2977 / 8234 : ℝ) + (-1 / 24702 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_1_1_3]
  have harg : (2 : ℝ) + ((2473 / 3229 : ℝ) + (1 / 3229 : ℝ) * Real.sqrt 3) = (8931 / 3229 : ℝ) + (1 / 3229 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (8931 / 3229 : ℝ) (1 / 3229 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_2_1_3 : prefixEval [2,1,3,3,2,1,3] lowerTau = (7295 / 20186 : ℝ) + (-1 / 60558 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_2_1_3]
  have harg : (2 : ℝ) + ((6067 / 7909 : ℝ) + (1 / 7909 : ℝ) * Real.sqrt 3) = (21885 / 7909 : ℝ) + (1 / 7909 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (21885 / 7909 : ℝ) (1 / 7909 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3_2_3 : prefixEval [2,1,3,3,3,2,3] lowerTau = (79369 / 219661 : ℝ) + (-1 / 219661 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_2_3]
  have harg : (2 : ℝ) + ((22013 / 28678 : ℝ) + (1 / 28678 : ℝ) * Real.sqrt 3) = (79369 / 28678 : ℝ) + (1 / 28678 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (79369 / 28678 : ℝ) (1 / 28678 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_1_1_1_3 : prefixEval [3,1,2,1,1,1,3] lowerTau = (593 / 2207 : ℝ) + (-1 / 6621 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_1_1_3]
  have harg : (3 : ℝ) + ((345 / 478 : ℝ) + (1 / 478 : ℝ) * Real.sqrt 3) = (1779 / 478 : ℝ) + (1 / 478 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1779 / 478 : ℝ) (1 / 478 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_1_3_1_2_1_1 : prefixEval [3,1,3,1,2,1,1] lowerTau = (3362 / 12743 : ℝ) + (1 / 12743 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1_1]
  have harg : (3 : ℝ) + ((701 / 887 : ℝ) + (-1 / 887 : ℝ) * Real.sqrt 3) = (3362 / 887 : ℝ) + (-1 / 887 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3362 / 887 : ℝ) (-1 / 887 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_1_2 : prefixEval [3,1,3,1,2,1,2] lowerTau = (21 / 73 : ℝ) + (-1 / 73 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1_2]
  have harg : (3 : ℝ) + ((1 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3) = (7 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (7 / 2 : ℝ) (1 / 6 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_1_3 : prefixEval [3,1,3,1,2,1,3] lowerTau = (6140 / 23257 : ℝ) + (-1 / 23257 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1_3]
  have harg : (3 : ℝ) + ((1277 / 1621 : ℝ) + (1 / 1621 : ℝ) * Real.sqrt 3) = (6140 / 1621 : ℝ) + (1 / 1621 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (6140 / 1621 : ℝ) (1 / 1621 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_3_1_2_1_3 : prefixEval [3,3,3,1,2,1,3] lowerTau = (35548 / 117517 : ℝ) + (-1 / 117517 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_1_2_1_3]
  have harg : (3 : ℝ) + ((3289 / 10753 : ℝ) + (1 / 10753 : ℝ) * Real.sqrt 3) = (35548 / 10753 : ℝ) + (1 / 10753 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (35548 / 10753 : ℝ) (1 / 10753 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_2_1_3 : prefixEval [1,2,1,3,1,2,1,3] lowerTau = (17117 / 23257 : ℝ) + (1 / 23257 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_2_1_3]
  have harg : (1 : ℝ) + ((4519 / 12598 : ℝ) + (-1 / 12598 : ℝ) * Real.sqrt 3) = (17117 / 12598 : ℝ) + (-1 / 12598 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (17117 / 12598 : ℝ) (-1 / 12598 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_2_1 : prefixEval [1,2,1,3,1,3,2,1] lowerTau = (18288 / 24841 : ℝ) + (-1 / 74523 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_2_1]
  have harg : (1 : ℝ) + ((14473 / 40391 : ℝ) + (1 / 40391 : ℝ) * Real.sqrt 3) = (54864 / 40391 : ℝ) + (1 / 40391 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (54864 / 40391 : ℝ) (1 / 40391 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_2_3 : prefixEval [1,2,1,3,1,3,2,3] lowerTau = (57934 / 78697 : ℝ) + (1 / 78697 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_2_3]
  have harg : (1 : ℝ) + ((15285 / 42649 : ℝ) + (-1 / 42649 : ℝ) * Real.sqrt 3) = (57934 / 42649 : ℝ) + (-1 / 42649 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (57934 / 42649 : ℝ) (-1 / 42649 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_1_1_3 : prefixEval [1,2,1,3,3,1,1,3] lowerTau = (33633 / 45793 : ℝ) + (1 / 45793 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_1_1_3]
  have harg : (1 : ℝ) + ((2977 / 8234 : ℝ) + (-1 / 24702 : ℝ) * Real.sqrt 3) = (11211 / 8234 : ℝ) + (-1 / 24702 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (11211 / 8234 : ℝ) (-1 / 24702 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_2_1_3 : prefixEval [1,2,1,3,3,2,1,3] lowerTau = (82443 / 112237 : ℝ) + (1 / 112237 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_2_1_3]
  have harg : (1 : ℝ) + ((7295 / 20186 : ℝ) + (-1 / 60558 : ℝ) * Real.sqrt 3) = (27481 / 20186 : ℝ) + (-1 / 60558 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (27481 / 20186 : ℝ) (-1 / 60558 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3_2_3 : prefixEval [1,2,1,3,3,3,2,3] lowerTau = (299030 / 407077 : ℝ) + (1 / 407077 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_2_3]
  have harg : (1 : ℝ) + ((79369 / 219661 : ℝ) + (-1 / 219661 : ℝ) * Real.sqrt 3) = (299030 / 219661 : ℝ) + (-1 / 219661 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (299030 / 219661 : ℝ) (-1 / 219661 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_1_1_1_3 : prefixEval [1,3,1,2,1,1,1,3] lowerTau = (8400 / 10657 : ℝ) + (1 / 10657 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_1_1_1_3]
  have harg : (1 : ℝ) + ((593 / 2207 : ℝ) + (-1 / 6621 : ℝ) * Real.sqrt 3) = (2800 / 2207 : ℝ) + (-1 / 6621 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2800 / 2207 : ℝ) (-1 / 6621 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_1_3_1_2_1_1 : prefixEval [1,3,1,3,1,2,1,1] lowerTau = (16105 / 20354 : ℝ) + (-1 / 20354 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_1_1]
  have harg : (1 : ℝ) + ((3362 / 12743 : ℝ) + (1 / 12743 : ℝ) * Real.sqrt 3) = (16105 / 12743 : ℝ) + (1 / 12743 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (16105 / 12743 : ℝ) (1 / 12743 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_1_2 : prefixEval [1,3,1,3,1,2,1,2] lowerTau = (94 / 121 : ℝ) + (1 / 121 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_1_2]
  have harg : (1 : ℝ) + ((21 / 73 : ℝ) + (-1 / 73 : ℝ) * Real.sqrt 3) = (94 / 73 : ℝ) + (-1 / 73 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (94 / 73 : ℝ) (-1 / 73 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_1_3 : prefixEval [1,3,1,3,1,2,1,3] lowerTau = (9799 / 12386 : ℝ) + (1 / 37158 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_1_3]
  have harg : (1 : ℝ) + ((6140 / 23257 : ℝ) + (-1 / 23257 : ℝ) * Real.sqrt 3) = (29397 / 23257 : ℝ) + (-1 / 23257 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (29397 / 23257 : ℝ) (-1 / 23257 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3_1_2_1_3 : prefixEval [1,3,3,3,1,2,1,3] lowerTau = (153065 / 199366 : ℝ) + (1 / 199366 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_1_2_1_3]
  have harg : (1 : ℝ) + ((35548 / 117517 : ℝ) + (-1 / 117517 : ℝ) * Real.sqrt 3) = (153065 / 117517 : ℝ) + (-1 / 117517 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (153065 / 117517 : ℝ) (-1 / 117517 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_2_1_3_1_3_2 : prefixEval [2,1,2,1,3,1,3,2] lowerTau = (6631 / 18142 : ℝ) + (-1 / 54426 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_3_1_3_2]
  have harg : (2 : ℝ) + ((5351 / 7271 : ℝ) + (1 / 7271 : ℝ) * Real.sqrt 3) = (19893 / 7271 : ℝ) + (1 / 7271 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (19893 / 7271 : ℝ) (1 / 7271 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_1 : prefixEval [2,1,3,1,3,1,2,1] lowerTau = (35979 / 100418 : ℝ) + (-1 / 100418 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_1]
  have harg : (2 : ℝ) + ((3399 / 4297 : ℝ) + (1 / 12891 : ℝ) * Real.sqrt 3) = (11993 / 4297 : ℝ) + (1 / 12891 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (11993 / 4297 : ℝ) (1 / 12891 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_2_1_3 : prefixEval [2,1,3,1,3,2,1,3] lowerTau = (45644 / 127369 : ℝ) + (1 / 127369 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_2_1_3]
  have harg : (2 : ℝ) + ((12930 / 16357 : ℝ) + (-1 / 16357 : ℝ) * Real.sqrt 3) = (45644 / 16357 : ℝ) + (-1 / 16357 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (45644 / 16357 : ℝ) (-1 / 16357 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_1_2_1_3 : prefixEval [2,1,3,3,1,2,1,3] lowerTau = (50716 / 140269 : ℝ) + (1 / 140269 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_1_2_1_3]
  have harg : (2 : ℝ) + ((14042 / 18337 : ℝ) + (-1 / 18337 : ℝ) * Real.sqrt 3) = (50716 / 18337 : ℝ) + (-1 / 18337 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (50716 / 18337 : ℝ) (-1 / 18337 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3_1_1_3 : prefixEval [2,1,3,3,3,1,1,3] lowerTau = (97184 / 268981 : ℝ) + (1 / 268981 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_1_1_3]
  have harg : (2 : ℝ) + ((26958 / 35113 : ℝ) + (-1 / 35113 : ℝ) * Real.sqrt 3) = (97184 / 35113 : ℝ) + (-1 / 35113 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (97184 / 35113 : ℝ) (-1 / 35113 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3_2_1_3 : prefixEval [2,1,3,3,3,2,1,3] lowerTau = (238562 / 660253 : ℝ) + (1 / 660253 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_2_1_3]
  have harg : (2 : ℝ) + ((66168 / 86197 : ℝ) + (-1 / 86197 : ℝ) * Real.sqrt 3) = (238562 / 86197 : ℝ) + (-1 / 86197 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (238562 / 86197 : ℝ) (-1 / 86197 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_1_1_1 : prefixEval [3,1,3,1,2,1,1,1] lowerTau = (3669 / 13897 : ℝ) + (-1 / 41691 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1_1_1]
  have harg : (3 : ℝ) + ((2289 / 2906 : ℝ) + (1 / 2906 : ℝ) * Real.sqrt 3) = (11007 / 2906 : ℝ) + (1 / 2906 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (11007 / 2906 : ℝ) (1 / 2906 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_1_1_3 : prefixEval [3,1,3,1,2,1,1,3] lowerTau = (14995 / 56809 : ℝ) + (1 / 56809 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1_1_3]
  have harg : (3 : ℝ) + ((3121 / 3958 : ℝ) + (-1 / 3958 : ℝ) * Real.sqrt 3) = (14995 / 3958 : ℝ) + (-1 / 3958 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (14995 / 3958 : ℝ) (-1 / 3958 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_1_2_3 : prefixEval [3,1,3,1,2,1,2,3] lowerTau = (26586 / 100729 : ℝ) + (1 / 100729 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1_2_3]
  have harg : (3 : ℝ) + ((1845 / 2339 : ℝ) + (-1 / 7017 : ℝ) * Real.sqrt 3) = (8862 / 2339 : ℝ) + (-1 / 7017 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (8862 / 2339 : ℝ) (-1 / 7017 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_2_1_2_1_3 : prefixEval [3,1,3,2,1,2,1,3] lowerTau = (38650 / 145753 : ℝ) + (1 / 145753 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_2_1_2_1_3]
  have harg : (3 : ℝ) + ((7903 / 10249 : ℝ) + (-1 / 10249 : ℝ) * Real.sqrt 3) = (38650 / 10249 : ℝ) + (-1 / 10249 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (38650 / 10249 : ℝ) (-1 / 10249 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_2_1_3_1_3_2 : prefixEval [1,2,1,2,1,3,1,3,2] lowerTau = (74319 / 101483 : ℝ) + (1 / 101483 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_2_1_3_1_3_2]
  have harg : (1 : ℝ) + ((6631 / 18142 : ℝ) + (-1 / 54426 : ℝ) * Real.sqrt 3) = (24773 / 18142 : ℝ) + (-1 / 54426 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (24773 / 18142 : ℝ) (-1 / 54426 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_1 : prefixEval [1,2,1,3,1,3,1,2,1] lowerTau = (136397 / 185267 : ℝ) + (1 / 185267 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_1]
  have harg : (1 : ℝ) + ((35979 / 100418 : ℝ) + (-1 / 100418 : ℝ) * Real.sqrt 3) = (136397 / 100418 : ℝ) + (-1 / 100418 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (136397 / 100418 : ℝ) (-1 / 100418 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_2_1_3 : prefixEval [1,2,1,3,1,3,2,1,3] lowerTau = (57671 / 78338 : ℝ) + (-1 / 235014 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_2_1_3]
  have harg : (1 : ℝ) + ((45644 / 127369 : ℝ) + (1 / 127369 : ℝ) * Real.sqrt 3) = (173013 / 127369 : ℝ) + (1 / 127369 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (173013 / 127369 : ℝ) (1 / 127369 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_1_2_1_3 : prefixEval [1,2,1,3,3,1,2,1,3] lowerTau = (190985 / 260038 : ℝ) + (-1 / 260038 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_1_2_1_3]
  have harg : (1 : ℝ) + ((50716 / 140269 : ℝ) + (1 / 140269 : ℝ) * Real.sqrt 3) = (190985 / 140269 : ℝ) + (1 / 140269 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (190985 / 140269 : ℝ) (1 / 140269 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3_1_1_3 : prefixEval [1,2,1,3,3,3,1,1,3] lowerTau = (122055 / 166154 : ℝ) + (-1 / 498462 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_1_1_3]
  have harg : (1 : ℝ) + ((97184 / 268981 : ℝ) + (1 / 268981 : ℝ) * Real.sqrt 3) = (366165 / 268981 : ℝ) + (1 / 268981 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (366165 / 268981 : ℝ) (1 / 268981 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3_2_1_3 : prefixEval [1,2,1,3,3,3,2,1,3] lowerTau = (299605 / 407858 : ℝ) + (-1 / 1223574 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_2_1_3]
  have harg : (1 : ℝ) + ((238562 / 660253 : ℝ) + (1 / 660253 : ℝ) * Real.sqrt 3) = (898815 / 660253 : ℝ) + (1 / 660253 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (898815 / 660253 : ℝ) (1 / 660253 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_1_1_1 : prefixEval [1,3,1,3,1,2,1,1,1] lowerTau = (52698 / 66611 : ℝ) + (1 / 66611 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_1_1_1]
  have harg : (1 : ℝ) + ((3669 / 13897 : ℝ) + (-1 / 41691 : ℝ) * Real.sqrt 3) = (17566 / 13897 : ℝ) + (-1 / 41691 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (17566 / 13897 : ℝ) (-1 / 41691 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_1_1_3 : prefixEval [1,3,1,3,1,2,1,1,3] lowerTau = (71804 / 90757 : ℝ) + (-1 / 90757 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_1_1_3]
  have harg : (1 : ℝ) + ((14995 / 56809 : ℝ) + (1 / 56809 : ℝ) * Real.sqrt 3) = (71804 / 56809 : ℝ) + (1 / 56809 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (71804 / 56809 : ℝ) (1 / 56809 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_1_2_3 : prefixEval [1,3,1,3,1,2,1,2,3] lowerTau = (127315 / 160918 : ℝ) + (-1 / 160918 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_1_2_3]
  have harg : (1 : ℝ) + ((26586 / 100729 : ℝ) + (1 / 100729 : ℝ) * Real.sqrt 3) = (127315 / 100729 : ℝ) + (1 / 100729 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (127315 / 100729 : ℝ) (1 / 100729 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_2_1_2_1_3 : prefixEval [1,3,1,3,2,1,2,1,3] lowerTau = (184403 / 233302 : ℝ) + (-1 / 233302 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_2_1_2_1_3]
  have harg : (1 : ℝ) + ((38650 / 145753 : ℝ) + (1 / 145753 : ℝ) * Real.sqrt 3) = (184403 / 145753 : ℝ) + (1 / 145753 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (184403 / 145753 : ℝ) (1 / 145753 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_2_1_3_1_3_2_1 : prefixEval [2,1,2,1,3,1,3,2,1] lowerTau = (203910 / 557939 : ℝ) + (1 / 557939 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_3_1_3_2_1]
  have harg : (2 : ℝ) + ((18288 / 24841 : ℝ) + (-1 / 74523 : ℝ) * Real.sqrt 3) = (67970 / 24841 : ℝ) + (-1 / 74523 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (67970 / 24841 : ℝ) (-1 / 74523 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_2_1_3_1_3_2_3 : prefixEval [2,1,2,1,3,1,3,2,3] lowerTau = (71776 / 196391 : ℝ) + (-1 / 589173 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_3_1_3_2_3]
  have harg : (2 : ℝ) + ((57934 / 78697 : ℝ) + (1 / 78697 : ℝ) * Real.sqrt 3) = (215328 / 78697 : ℝ) + (1 / 78697 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (215328 / 78697 : ℝ) (1 / 78697 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_1_1 : prefixEval [2,1,3,1,3,1,2,1,1] lowerTau = (56813 / 158579 : ℝ) + (1 / 158579 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_1_1]
  have harg : (2 : ℝ) + ((16105 / 20354 : ℝ) + (-1 / 20354 : ℝ) * Real.sqrt 3) = (56813 / 20354 : ℝ) + (-1 / 20354 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (56813 / 20354 : ℝ) (-1 / 20354 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_1_2 : prefixEval [2,1,3,1,3,1,2,1,2] lowerTau = (112 / 311 : ℝ) + (-1 / 933 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_1_2]
  have harg : (2 : ℝ) + ((94 / 121 : ℝ) + (1 / 121 : ℝ) * Real.sqrt 3) = (336 / 121 : ℝ) + (1 / 121 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (336 / 121 : ℝ) (1 / 121 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_1_3 : prefixEval [2,1,3,1,3,1,2,1,3] lowerTau = (103713 / 289477 : ℝ) + (-1 / 289477 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_1_3]
  have harg : (2 : ℝ) + ((9799 / 12386 : ℝ) + (1 / 37158 : ℝ) * Real.sqrt 3) = (34571 / 12386 : ℝ) + (1 / 37158 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (34571 / 12386 : ℝ) (1 / 37158 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3_1_2_1_3 : prefixEval [2,1,3,3,3,1,2,1,3] lowerTau = (551797 / 1527241 : ℝ) + (-1 / 1527241 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_1_2_1_3]
  have harg : (2 : ℝ) + ((153065 / 199366 : ℝ) + (1 / 199366 : ℝ) * Real.sqrt 3) = (551797 / 199366 : ℝ) + (1 / 199366 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (551797 / 199366 : ℝ) (1 / 199366 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_1_1_1_3 : prefixEval [3,1,3,1,2,1,1,1,3] lowerTau = (13457 / 50978 : ℝ) + (-1 / 152934 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1_1_1_3]
  have harg : (3 : ℝ) + ((8400 / 10657 : ℝ) + (1 / 10657 : ℝ) * Real.sqrt 3) = (40371 / 10657 : ℝ) + (1 / 10657 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (40371 / 10657 : ℝ) (1 / 10657 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_1_2_1_3 : prefixEval [3,1,3,1,2,1,2,1,3] lowerTau = (28431 / 107714 : ℝ) + (-1 / 323142 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_1_2_1_3]
  have harg : (3 : ℝ) + ((17754 / 22513 : ℝ) + (1 / 22513 : ℝ) * Real.sqrt 3) = (85293 / 22513 : ℝ) + (1 / 22513 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (85293 / 22513 : ℝ) (1 / 22513 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_2_1_3_1_3_2_1 : prefixEval [1,2,1,2,1,3,1,3,2,1] lowerTau = (761849 / 1040282 : ℝ) + (-1 / 1040282 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_2_1_3_1_3_2_1]
  have harg : (1 : ℝ) + ((203910 / 557939 : ℝ) + (1 / 557939 : ℝ) * Real.sqrt 3) = (761849 / 557939 : ℝ) + (1 / 557939 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (761849 / 557939 : ℝ) (1 / 557939 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_2_1_3_1_3_2_3 : prefixEval [1,2,1,2,1,3,1,3,2,3] lowerTau = (804501 / 1098526 : ℝ) + (1 / 1098526 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_2_1_3_1_3_2_3]
  have harg : (1 : ℝ) + ((71776 / 196391 : ℝ) + (-1 / 589173 : ℝ) * Real.sqrt 3) = (268167 / 196391 : ℝ) + (-1 / 589173 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (268167 / 196391 : ℝ) (-1 / 589173 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_1_1 : prefixEval [1,2,1,3,1,3,1,2,1,1] lowerTau = (215392 / 292559 : ℝ) + (-1 / 292559 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_1_1]
  have harg : (1 : ℝ) + ((56813 / 158579 : ℝ) + (1 / 158579 : ℝ) * Real.sqrt 3) = (215392 / 158579 : ℝ) + (1 / 158579 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (215392 / 158579 : ℝ) (1 / 158579 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_1_2 : prefixEval [1,2,1,3,1,3,1,2,1,2] lowerTau = (1269 / 1726 : ℝ) + (1 / 1726 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_1_2]
  have harg : (1 : ℝ) + ((112 / 311 : ℝ) + (-1 / 933 : ℝ) * Real.sqrt 3) = (423 / 311 : ℝ) + (-1 / 933 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (423 / 311 : ℝ) (-1 / 933 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_1_3 : prefixEval [1,2,1,3,1,3,1,2,1,3] lowerTau = (393190 / 534061 : ℝ) + (1 / 534061 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_1_3]
  have harg : (1 : ℝ) + ((103713 / 289477 : ℝ) + (-1 / 289477 : ℝ) * Real.sqrt 3) = (393190 / 289477 : ℝ) + (-1 / 289477 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (393190 / 289477 : ℝ) (-1 / 289477 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3_1_2_1_3 : prefixEval [1,2,1,3,3,3,1,2,1,3] lowerTau = (2079038 / 2830201 : ℝ) + (1 / 2830201 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_1_2_1_3]
  have harg : (1 : ℝ) + ((551797 / 1527241 : ℝ) + (-1 / 1527241 : ℝ) * Real.sqrt 3) = (2079038 / 1527241 : ℝ) + (-1 / 1527241 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2079038 / 1527241 : ℝ) (-1 / 1527241 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_1_1_1_3 : prefixEval [1,3,1,3,1,2,1,1,1,3] lowerTau = (193305 / 244333 : ℝ) + (1 / 244333 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_1_1_1_3]
  have harg : (1 : ℝ) + ((13457 / 50978 : ℝ) + (-1 / 152934 : ℝ) * Real.sqrt 3) = (64435 / 50978 : ℝ) + (-1 / 152934 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (64435 / 50978 : ℝ) (-1 / 152934 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_1_2_1_3 : prefixEval [1,3,1,3,1,2,1,2,1,3] lowerTau = (408435 / 516241 : ℝ) + (1 / 516241 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_1_2_1_3]
  have harg : (1 : ℝ) + ((28431 / 107714 : ℝ) + (-1 / 323142 : ℝ) * Real.sqrt 3) = (136145 / 107714 : ℝ) + (-1 / 323142 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (136145 / 107714 : ℝ) (-1 / 323142 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_2_1_3_1_3_2_1_3 : prefixEval [2,1,2,1,3,1,3,2,1,3] lowerTau = (643041 / 1759477 : ℝ) + (1 / 1759477 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_3_1_3_2_1_3]
  have harg : (2 : ℝ) + ((57671 / 78338 : ℝ) + (-1 / 235014 : ℝ) * Real.sqrt 3) = (214347 / 78338 : ℝ) + (-1 / 235014 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (214347 / 78338 : ℝ) (-1 / 235014 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_1_1_1 : prefixEval [2,1,3,1,3,1,2,1,1,1] lowerTau = (185920 / 518927 : ℝ) + (-1 / 518927 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_1_1_1]
  have harg : (2 : ℝ) + ((52698 / 66611 : ℝ) + (1 / 66611 : ℝ) * Real.sqrt 3) = (185920 / 66611 : ℝ) + (1 / 66611 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (185920 / 66611 : ℝ) (1 / 66611 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_1_1_3 : prefixEval [2,1,3,1,3,1,2,1,1,3] lowerTau = (253318 / 707053 : ℝ) + (1 / 707053 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_1_1_3]
  have harg : (2 : ℝ) + ((71804 / 90757 : ℝ) + (-1 / 90757 : ℝ) * Real.sqrt 3) = (253318 / 90757 : ℝ) + (-1 / 90757 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (253318 / 90757 : ℝ) (-1 / 90757 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_1_2_3 : prefixEval [2,1,3,1,3,1,2,1,2,3] lowerTau = (149717 / 417887 : ℝ) + (1 / 1253661 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_1_2_3]
  have harg : (2 : ℝ) + ((127315 / 160918 : ℝ) + (-1 / 160918 : ℝ) * Real.sqrt 3) = (449151 / 160918 : ℝ) + (-1 / 160918 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (449151 / 160918 : ℝ) (-1 / 160918 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_2_1_2_1_3 : prefixEval [2,1,3,1,3,2,1,2,1,3] lowerTau = (651007 / 1816573 : ℝ) + (1 / 1816573 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_2_1_2_1_3]
  have harg : (2 : ℝ) + ((184403 / 233302 : ℝ) + (-1 / 233302 : ℝ) * Real.sqrt 3) = (651007 / 233302 : ℝ) + (-1 / 233302 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (651007 / 233302 : ℝ) (-1 / 233302 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_2_1_3_1_3_2_1_3 : prefixEval [1,2,1,2,1,3,1,3,2,1,3] lowerTau = (2402518 / 3280573 : ℝ) + (-1 / 3280573 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_2_1_3_1_3_2_1_3]
  have harg : (1 : ℝ) + ((643041 / 1759477 : ℝ) + (1 / 1759477 : ℝ) * Real.sqrt 3) = (2402518 / 1759477 : ℝ) + (1 / 1759477 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2402518 / 1759477 : ℝ) (1 / 1759477 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_1_1_1 : prefixEval [1,2,1,3,1,3,1,2,1,1,1] lowerTau = (234949 / 319126 : ℝ) + (1 / 957378 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_1_1_1]
  have harg : (1 : ℝ) + ((185920 / 518927 : ℝ) + (-1 / 518927 : ℝ) * Real.sqrt 3) = (704847 / 518927 : ℝ) + (-1 / 518927 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (704847 / 518927 : ℝ) (-1 / 518927 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_1_1_3 : prefixEval [1,2,1,3,1,3,1,2,1,1,3] lowerTau = (960371 / 1304446 : ℝ) + (-1 / 1304446 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_1_1_3]
  have harg : (1 : ℝ) + ((253318 / 707053 : ℝ) + (1 / 707053 : ℝ) * Real.sqrt 3) = (960371 / 707053 : ℝ) + (1 / 707053 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (960371 / 707053 : ℝ) (1 / 707053 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_1_2_3 : prefixEval [1,2,1,3,1,3,1,2,1,2,3] lowerTau = (1702812 / 2312881 : ℝ) + (-1 / 2312881 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_1_2_3]
  have harg : (1 : ℝ) + ((149717 / 417887 : ℝ) + (1 / 1253661 : ℝ) * Real.sqrt 3) = (567604 / 417887 : ℝ) + (1 / 1253661 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (567604 / 417887 : ℝ) (1 / 1253661 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_2_1_2_1_3 : prefixEval [1,2,1,3,1,3,2,1,2,1,3] lowerTau = (2467580 / 3351889 : ℝ) + (-1 / 3351889 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_2_1_2_1_3]
  have harg : (1 : ℝ) + ((651007 / 1816573 : ℝ) + (1 / 1816573 : ℝ) * Real.sqrt 3) = (2467580 / 1816573 : ℝ) + (1 / 1816573 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2467580 / 1816573 : ℝ) (1 / 1816573 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_1_1_1_3 : prefixEval [2,1,3,1,3,1,2,1,1,1,3] lowerTau = (681971 / 1903486 : ℝ) + (-1 / 1903486 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_1_1_1_3]
  have harg : (2 : ℝ) + ((193305 / 244333 : ℝ) + (1 / 244333 : ℝ) * Real.sqrt 3) = (681971 / 244333 : ℝ) + (1 / 244333 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (681971 / 244333 : ℝ) (1 / 244333 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_1_2_1_3 : prefixEval [2,1,3,1,3,1,2,1,2,1,3] lowerTau = (1440917 / 4021846 : ℝ) + (-1 / 4021846 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_1_2_1_3]
  have harg : (2 : ℝ) + ((408435 / 516241 : ℝ) + (1 / 516241 : ℝ) * Real.sqrt 3) = (1440917 / 516241 : ℝ) + (1 / 516241 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1440917 / 516241 : ℝ) (1 / 516241 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_1_1_1_3 : prefixEval [1,2,1,3,1,3,1,2,1,1,1,3] lowerTau = (861819 / 1170587 : ℝ) + (1 / 3511761 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_1_1_1_3]
  have harg : (1 : ℝ) + ((681971 / 1903486 : ℝ) + (-1 / 1903486 : ℝ) * Real.sqrt 3) = (2585457 / 1903486 : ℝ) + (-1 / 1903486 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2585457 / 1903486 : ℝ) (-1 / 1903486 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_1_2_1_3 : prefixEval [1,2,1,3,1,3,1,2,1,2,1,3] lowerTau = (1820921 / 2473307 : ℝ) + (1 / 7419921 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_1_2_1_3]
  have harg : (1 : ℝ) + ((1440917 / 4021846 : ℝ) + (-1 / 4021846 : ℝ) * Real.sqrt 3) = (5462763 / 4021846 : ℝ) + (-1 / 4021846 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5462763 / 4021846 : ℝ) (-1 / 4021846 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_2_1_3_1_3_2_1_2_1_3 : prefixEval [2,1,2,1,3,1,3,2,1,2,1,3] lowerTau = (9171358 / 25094449 : ℝ) + (1 / 25094449 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_1_3_1_3_2_1_2_1_3]
  have harg : (2 : ℝ) + ((2467580 / 3351889 : ℝ) + (-1 / 3351889 : ℝ) * Real.sqrt 3) = (9171358 / 3351889 : ℝ) + (-1 / 3351889 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (9171358 / 3351889 : ℝ) (-1 / 3351889 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_2_1_3_1_3_2_1_2_1_3 : prefixEval [1,2,1,2,1,3,1,3,2,1,2,1,3] lowerTau = (34265807 / 46789054 : ℝ) + (-1 / 46789054 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_2_1_3_1_3_2_1_2_1_3]
  have harg : (1 : ℝ) + ((9171358 / 25094449 : ℝ) + (1 / 25094449 : ℝ) * Real.sqrt 3) = (34265807 / 25094449 : ℝ) + (1 / 25094449 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (34265807 / 25094449 : ℝ) (1 / 25094449 : ℝ) (by norm_num)]
  norm_num
  ring

set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
private theorem bridge_sqrt3_cube : (Real.sqrt 3)^3 = 3 * Real.sqrt 3 := by
  calc (Real.sqrt 3)^3 = (Real.sqrt 3)^2 * Real.sqrt 3 := by ring
    _ = 3 * Real.sqrt 3 := by rw [Real.sq_sqrt (by norm_num)]

private theorem bridge_bc : LowerInitialFamily.B ≠ LowerInitialFamily.C := by intro h; cases h
private theorem bridge_ac : LowerInitialFamily.A ≠ LowerInitialFamily.C := by intro h; cases h

private theorem bridge_aPos_0 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[0]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[0]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_1 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[1]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[1]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_2 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[2]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[2]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_3 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[3]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[3]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_4 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[4]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[4]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_5 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[5]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[5]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_6 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[6]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[6]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_7 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[7]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[7]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_8 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[8]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[8]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_9 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[9]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[9]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_10 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[10]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[10]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_11 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[11]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[11]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_12 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[12]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[12]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_13 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[13]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[13]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_14 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[14]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[14]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_15 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[15]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[15]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_16 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[16]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[16]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_17 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[17]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[17]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_18 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[18]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[18]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_19 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[19]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[19]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_20 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[20]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[20]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_21 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[21]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[21]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_22 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[22]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[22]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_23 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[23]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[23]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_24 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[24]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[24]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_25 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[25]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[25]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_26 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[26]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[26]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_27 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[27]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[27]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_28 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[28]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[28]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_29 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[29]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[29]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_30 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[30]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[30]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_31 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[31]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[31]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_32 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[32]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[32]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_33 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[33]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[33]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_34 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[34]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[34]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_35 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[35]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[35]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_36 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[36]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[36]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_37 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[37]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[37]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_38 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[38]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[38]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_39 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[39]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[39]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_40 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[40]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[40]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_41 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[41]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[41]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_42 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[42]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[42]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_43 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[43]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[43]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_44 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[44]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[44]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_45 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[45]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[45]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_46 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[46]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[46]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_47 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[47]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[47]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_48 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[48]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[48]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_49 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[49]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[49]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_50 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[50]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[50]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_51 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[51]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[51]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_52 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[52]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[52]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_53 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[53]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[53]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_54 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[54]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[54]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_55 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[55]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[55]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_56 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[56]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[56]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_57 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[57]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[57]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_58 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[58]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[58]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_59 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[59]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[59]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring


private theorem bridge_aPos_60 (x y : ℝ) :
    certPolyEval (lowerBridgeRecords_aPos[60]'(by decide)).polynomial x y =
      lowerBridgeNumerator .aPos (lowerBridgeRecords_aPos[60]'(by decide)) x y := by
  norm_num [lowerBridgeRecords_aPos, certPolyEval, certFieldVal, Fin.sum_univ_succ,
    lowerBridgeNumerator, lowerBridgeMatrices, lowerBridgeSeamCase, lowerBridgeFamily,
    lowerInitialSeamFamily, bridge_bc, bridge_ac, lowerInitialSeamMatrices, lowerInitialSeamZero,
    lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialP, lowerInitialK, lowerInitialKPrev,
    lowerBridgeMatAppend, lowerBridgeWidthDen, lowerInitialMatDen,
    List.foldl_cons, List.foldl_nil, lowerAlpha, lowerBeta, lowerTheta, lowerBridgeDifference, lowerBridgeCommonMatrices, lowerBridgeZero, bp_nil, bp_1, bp_2, bp_3, bp_1_1, bp_1_2, bp_1_3, bp_2_1, bp_2_3, bp_3_1, bp_3_2, bp_3_3, bp_1_1_1, bp_1_1_3, bp_1_2_1, bp_1_2_3, bp_1_3_1, bp_1_3_2, bp_1_3_3, bp_2_1_1, bp_2_1_2, bp_2_1_3, bp_3_2_1, bp_3_2_3, bp_3_3_1, bp_3_3_2, bp_3_3_3, bp_1_1_1_3, bp_1_2_1_1, bp_1_2_1_2, bp_1_2_1_3, bp_1_3_2_1, bp_1_3_2_3, bp_1_3_3_1, bp_1_3_3_2, bp_1_3_3_3, bp_2_1_1_1, bp_2_1_1_3, bp_2_1_2_3, bp_2_1_3_1, bp_2_1_3_2, bp_2_1_3_3, bp_3_1_1_3, bp_3_1_2_1, bp_3_1_3_2, bp_3_2_1_3, bp_3_3_2_3, bp_3_3_3_1, bp_3_3_3_2, bp_3_3_3_3, bp_1_2_1_1_1, bp_1_2_1_1_3, bp_1_2_1_2_3, bp_1_2_1_3_1, bp_1_2_1_3_2, bp_1_2_1_3_3, bp_1_3_1_1_3, bp_1_3_1_2_1, bp_1_3_1_3_2, bp_1_3_2_1_3, bp_1_3_3_2_3, bp_1_3_3_3_1, bp_1_3_3_3_2, bp_1_3_3_3_3, bp_2_1_1_1_3, bp_2_1_2_1_3, bp_2_1_3_2_3, bp_2_1_3_3_1, bp_2_1_3_3_2, bp_2_1_3_3_3, bp_3_1_2_1_1, bp_3_1_2_1_2, bp_3_1_2_1_3, bp_3_1_3_2_1, bp_3_1_3_2_3, bp_3_3_1_1_3, bp_3_3_2_1_3, bp_3_3_3_2_3, bp_1_2_1_1_1_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_1, bp_1_2_1_3_3_2, bp_1_2_1_3_3_3, bp_1_3_1_2_1_1, bp_1_3_1_2_1_2, bp_1_3_1_2_1_3, bp_1_3_1_3_2_1, bp_1_3_1_3_2_3, bp_1_3_3_1_1_3, bp_1_3_3_2_1_3, bp_1_3_3_3_2_3, bp_2_1_3_1_1_3, bp_2_1_3_1_3_2, bp_2_1_3_2_1_3, bp_2_1_3_3_2_3, bp_2_1_3_3_3_1, bp_2_1_3_3_3_2, bp_2_1_3_3_3_3, bp_3_1_2_1_1_1, bp_3_1_2_1_1_3, bp_3_1_2_1_2_3, bp_3_1_3_1_2_1, bp_3_1_3_2_1_3, bp_3_2_1_2_1_3, bp_3_3_1_2_1_3, bp_3_3_3_1_1_3, bp_3_3_3_2_1_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_1_3_2, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_1, bp_1_2_1_3_3_3_2, bp_1_2_1_3_3_3_3, bp_1_3_1_2_1_1_1, bp_1_3_1_2_1_1_3, bp_1_3_1_2_1_2_3, bp_1_3_1_3_1_2_1, bp_1_3_1_3_2_1_3, bp_1_3_2_1_2_1_3, bp_1_3_3_1_2_1_3, bp_1_3_3_3_1_1_3, bp_1_3_3_3_2_1_3, bp_2_1_3_1_2_1_3, bp_2_1_3_1_3_2_1, bp_2_1_3_1_3_2_3, bp_2_1_3_3_1_1_3, bp_2_1_3_3_2_1_3, bp_2_1_3_3_3_2_3, bp_3_1_2_1_1_1_3, bp_3_1_2_1_2_1_3, bp_3_1_3_1_2_1_1, bp_3_1_3_1_2_1_2, bp_3_1_3_1_2_1_3, bp_3_3_3_1_2_1_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_1_3_2_1, bp_1_2_1_3_1_3_2_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_3_1_2_1_1_1_3, bp_1_3_1_2_1_2_1_3, bp_1_3_1_3_1_2_1_1, bp_1_3_1_3_1_2_1_2, bp_1_3_1_3_1_2_1_3, bp_1_3_3_3_1_2_1_3, bp_2_1_2_1_3_1_3_2, bp_2_1_3_1_3_1_2_1, bp_2_1_3_1_3_2_1_3, bp_2_1_3_3_1_2_1_3, bp_2_1_3_3_3_1_1_3, bp_2_1_3_3_3_2_1_3, bp_3_1_3_1_2_1_1_1, bp_3_1_3_1_2_1_1_3, bp_3_1_3_1_2_1_2_3, bp_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2, bp_1_2_1_3_1_3_1_2_1, bp_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_3_1_3_1_2_1_1_1, bp_1_3_1_3_1_2_1_1_3, bp_1_3_1_3_1_2_1_2_3, bp_1_3_1_3_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1, bp_2_1_2_1_3_1_3_2_3, bp_2_1_3_1_3_1_2_1_1, bp_2_1_3_1_3_1_2_1_2, bp_2_1_3_1_3_1_2_1_3, bp_2_1_3_3_3_1_2_1_3, bp_3_1_3_1_2_1_1_1_3, bp_3_1_3_1_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_1_1, bp_1_2_1_3_1_3_1_2_1_2, bp_1_2_1_3_1_3_1_2_1_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_3_1_3_1_2_1_1_1_3, bp_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_3, bp_2_1_3_1_3_1_2_1_1_1, bp_2_1_3_1_3_1_2_1_1_3, bp_2_1_3_1_3_1_2_1_2_3, bp_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1, bp_1_2_1_3_1_3_1_2_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_3, bp_1_2_1_3_1_3_2_1_2_1_3, bp_2_1_3_1_3_1_2_1_1_1_3, bp_2_1_3_1_3_1_2_1_2_1_3, bp_1_2_1_3_1_3_1_2_1_1_1_3, bp_1_2_1_3_1_3_1_2_1_2_1_3, bp_2_1_2_1_3_1_3_2_1_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_2_1_3]
  try simp only [prefixEval, lowerTau]
  try ring_nf
  norm_num [Real.sq_sqrt, bridge_sqrt3_cube]
  ring



theorem solution : ∀ r ∈ lowerBridgeRecords .aPos, ∀ x y : ℝ,
    certPolyEval r.polynomial x y = lowerBridgeNumerator .aPos r x y := by
  intro r hr x y
  simp only [lowerBridgeRecords, lowerBridgeRecords_aPos, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bridge_aPos_0 x y
  · exact bridge_aPos_1 x y
  · exact bridge_aPos_2 x y
  · exact bridge_aPos_3 x y
  · exact bridge_aPos_4 x y
  · exact bridge_aPos_5 x y
  · exact bridge_aPos_6 x y
  · exact bridge_aPos_7 x y
  · exact bridge_aPos_8 x y
  · exact bridge_aPos_9 x y
  · exact bridge_aPos_10 x y
  · exact bridge_aPos_11 x y
  · exact bridge_aPos_12 x y
  · exact bridge_aPos_13 x y
  · exact bridge_aPos_14 x y
  · exact bridge_aPos_15 x y
  · exact bridge_aPos_16 x y
  · exact bridge_aPos_17 x y
  · exact bridge_aPos_18 x y
  · exact bridge_aPos_19 x y
  · exact bridge_aPos_20 x y
  · exact bridge_aPos_21 x y
  · exact bridge_aPos_22 x y
  · exact bridge_aPos_23 x y
  · exact bridge_aPos_24 x y
  · exact bridge_aPos_25 x y
  · exact bridge_aPos_26 x y
  · exact bridge_aPos_27 x y
  · exact bridge_aPos_28 x y
  · exact bridge_aPos_29 x y
  · exact bridge_aPos_30 x y
  · exact bridge_aPos_31 x y
  · exact bridge_aPos_32 x y
  · exact bridge_aPos_33 x y
  · exact bridge_aPos_34 x y
  · exact bridge_aPos_35 x y
  · exact bridge_aPos_36 x y
  · exact bridge_aPos_37 x y
  · exact bridge_aPos_38 x y
  · exact bridge_aPos_39 x y
  · exact bridge_aPos_40 x y
  · exact bridge_aPos_41 x y
  · exact bridge_aPos_42 x y
  · exact bridge_aPos_43 x y
  · exact bridge_aPos_44 x y
  · exact bridge_aPos_45 x y
  · exact bridge_aPos_46 x y
  · exact bridge_aPos_47 x y
  · exact bridge_aPos_48 x y
  · exact bridge_aPos_49 x y
  · exact bridge_aPos_50 x y
  · exact bridge_aPos_51 x y
  · exact bridge_aPos_52 x y
  · exact bridge_aPos_53 x y
  · exact bridge_aPos_54 x y
  · exact bridge_aPos_55 x y
  · exact bridge_aPos_56 x y
  · exact bridge_aPos_57 x y
  · exact bridge_aPos_58 x y
  · exact bridge_aPos_59 x y
  · exact bridge_aPos_60 x y

#print axioms solution
