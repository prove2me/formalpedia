-- Prove2me | solution 1 for Freiman.lower_bridge_tau_values
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:09:13.208743+00:00
-- url     : https://prove2.me/submissions/7dffc47d-1d55-41e2-bcd5-23d0e073a1cd

import Definitions.Def_Freiman_lowerSelection
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

@[simp] private theorem bp_3 : prefixEval [3] lowerTau = (2 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_nil]
  have harg : (3 : ℝ) + ((-1 : ℝ) + (1 : ℝ) * Real.sqrt 3) = (2 : ℝ) + (1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2 : ℝ) (1 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_2_3 : prefixEval [3,2,3] lowerTau = (43 / 142 : ℝ) + (-1 / 142 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_3]
  have harg : (3 : ℝ) + ((4 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3) = (43 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (43 / 13 : ℝ) (1 / 13 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_2_3 : prefixEval [1,3,2,3] lowerTau = (185 / 241 : ℝ) + (1 / 241 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_2_3]
  have harg : (1 : ℝ) + ((43 / 142 : ℝ) + (-1 / 142 : ℝ) * Real.sqrt 3) = (185 / 142 : ℝ) + (-1 / 142 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (185 / 142 : ℝ) (-1 / 142 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_1_3 : prefixEval [2,1,1,3] lowerTau = (35 / 94 : ℝ) + (1 / 94 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_1_3]
  have harg : (2 : ℝ) + ((9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3) = (35 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (35 / 13 : ℝ) (-1 / 13 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_2_1_3 : prefixEval [2,2,1,3] lowerTau = (89 / 214 : ℝ) + (1 / 214 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3]
  have harg : (2 : ℝ) + ((15 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3) = (89 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (89 / 37 : ℝ) (-1 / 37 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_2_2_3 : prefixEval [2,2,2,3] lowerTau = (168 / 409 : ℝ) + (1 / 409 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_2_3]
  have harg : (2 : ℝ) + ((10 / 23 : ℝ) + (-1 / 69 : ℝ) * Real.sqrt 3) = (56 / 23 : ℝ) + (-1 / 69 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (56 / 23 : ℝ) (-1 / 69 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_3_3_3 : prefixEval [3,3,3,3] lowerTau = (758 / 2509 : ℝ) + (1 / 2509 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3]
  have harg : (3 : ℝ) + ((71 / 229 : ℝ) + (-1 / 229 : ℝ) * Real.sqrt 3) = (758 / 229 : ℝ) + (-1 / 229 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (758 / 229 : ℝ) (-1 / 229 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_2_1_3 : prefixEval [1,2,2,1,3] lowerTau = (101 / 143 : ℝ) + (-1 / 429 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_2_1_3]
  have harg : (1 : ℝ) + ((89 / 214 : ℝ) + (1 / 214 : ℝ) * Real.sqrt 3) = (303 / 214 : ℝ) + (1 / 214 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (303 / 214 : ℝ) (1 / 214 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_2_2_3 : prefixEval [1,2,2,2,3] lowerTau = (577 / 814 : ℝ) + (-1 / 814 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_2_2_3]
  have harg : (1 : ℝ) + ((168 / 409 : ℝ) + (1 / 409 : ℝ) * Real.sqrt 3) = (577 / 409 : ℝ) + (1 / 409 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (577 / 409 : ℝ) (1 / 409 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_3_3_3 : prefixEval [1,3,3,3,3] lowerTau = (1089 / 1418 : ℝ) + (-1 / 4254 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_3]
  have harg : (1 : ℝ) + ((758 / 2509 : ℝ) + (1 / 2509 : ℝ) * Real.sqrt 3) = (3267 / 2509 : ℝ) + (1 / 2509 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3267 / 2509 : ℝ) (1 / 2509 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_3_3_3 : prefixEval [2,1,3,3,3] lowerTau = (1086 / 3001 : ℝ) + (-1 / 3001 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3]
  have harg : (2 : ℝ) + ((100 / 131 : ℝ) + (1 / 393 : ℝ) * Real.sqrt 3) = (362 / 131 : ℝ) + (1 / 393 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (362 / 131 : ℝ) (1 / 393 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_2_1_1_3 : prefixEval [2,2,1,1,3] lowerTau = (223 / 529 : ℝ) + (-1 / 529 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_1_3]
  have harg : (2 : ℝ) + ((35 / 94 : ℝ) + (1 / 94 : ℝ) * Real.sqrt 3) = (223 / 94 : ℝ) + (1 / 94 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (223 / 94 : ℝ) (1 / 94 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_2_2_1_3 : prefixEval [2,2,2,1,3] lowerTau = (517 / 1249 : ℝ) + (-1 / 1249 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_2_1_3]
  have harg : (2 : ℝ) + ((89 / 214 : ℝ) + (1 / 214 : ℝ) * Real.sqrt 3) = (517 / 214 : ℝ) + (1 / 214 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (517 / 214 : ℝ) (1 / 214 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_1_2_2_3 : prefixEval [3,1,2,2,3] lowerTau = (175 / 647 : ℝ) + (-1 / 1941 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_2_3]
  have harg : (3 : ℝ) + ((99 / 142 : ℝ) + (1 / 142 : ℝ) * Real.sqrt 3) = (525 / 142 : ℝ) + (1 / 142 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (525 / 142 : ℝ) (1 / 142 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_3_3_3_3 : prefixEval [3,3,3,3,3] lowerTau = (8285 / 27358 : ℝ) + (-1 / 27358 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_3]
  have harg : (3 : ℝ) + ((758 / 2509 : ℝ) + (1 / 2509 : ℝ) * Real.sqrt 3) = (8285 / 2509 : ℝ) + (1 / 2509 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (8285 / 2509 : ℝ) (1 / 2509 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1_3_3_3 : prefixEval [1,2,1,3,3,3] lowerTau = (4087 / 5566 : ℝ) + (1 / 5566 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3]
  have harg : (1 : ℝ) + ((1086 / 3001 : ℝ) + (-1 / 3001 : ℝ) * Real.sqrt 3) = (4087 / 3001 : ℝ) + (-1 / 3001 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (4087 / 3001 : ℝ) (-1 / 3001 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_2_1_1_3 : prefixEval [1,2,2,1,1,3] lowerTau = (752 / 1069 : ℝ) + (1 / 1069 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_2_1_1_3]
  have harg : (1 : ℝ) + ((223 / 529 : ℝ) + (-1 / 529 : ℝ) * Real.sqrt 3) = (752 / 529 : ℝ) + (-1 / 529 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (752 / 529 : ℝ) (-1 / 529 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_2_2_1_3 : prefixEval [1,2,2,2,1,3] lowerTau = (1766 / 2497 : ℝ) + (1 / 2497 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_2_2_1_3]
  have harg : (1 : ℝ) + ((517 / 1249 : ℝ) + (-1 / 1249 : ℝ) * Real.sqrt 3) = (1766 / 1249 : ℝ) + (-1 / 1249 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1766 / 1249 : ℝ) (-1 / 1249 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_1_2_2_3 : prefixEval [1,3,1,2,2,3] lowerTau = (2466 / 3133 : ℝ) + (1 / 3133 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_2_3]
  have harg : (1 : ℝ) + ((175 / 647 : ℝ) + (-1 / 1941 : ℝ) * Real.sqrt 3) = (822 / 647 : ℝ) + (-1 / 1941 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (822 / 647 : ℝ) (-1 / 1941 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_3_3_3_3 : prefixEval [1,3,3,3,3,3] lowerTau = (11881 / 15479 : ℝ) + (1 / 46437 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_3_3]
  have harg : (1 : ℝ) + ((8285 / 27358 : ℝ) + (-1 / 27358 : ℝ) * Real.sqrt 3) = (35643 / 27358 : ℝ) + (-1 / 27358 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (35643 / 27358 : ℝ) (-1 / 27358 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_3_3_3_3 : prefixEval [2,1,3,3,3,3] lowerTau = (11775 / 32593 : ℝ) + (1 / 32593 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_3]
  have harg : (2 : ℝ) + ((1089 / 1418 : ℝ) + (-1 / 4254 : ℝ) * Real.sqrt 3) = (3925 / 1418 : ℝ) + (-1 / 4254 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3925 / 1418 : ℝ) (-1 / 4254 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_2_1_3 : prefixEval [3,1,2,2,1,3] lowerTau = (1590 / 5893 : ℝ) + (1 / 5893 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_2_1_3]
  have harg : (3 : ℝ) + ((101 / 143 : ℝ) + (-1 / 429 : ℝ) * Real.sqrt 3) = (530 / 143 : ℝ) + (-1 / 429 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (530 / 143 : ℝ) (-1 / 429 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_2_2_3 : prefixEval [3,1,2,2,2,3] lowerTau = (3019 / 11197 : ℝ) + (1 / 11197 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_2_2_3]
  have harg : (3 : ℝ) + ((577 / 814 : ℝ) + (-1 / 814 : ℝ) * Real.sqrt 3) = (3019 / 814 : ℝ) + (-1 / 814 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3019 / 814 : ℝ) (-1 / 814 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_3_3_3_2_3 : prefixEval [3,3,3,3,2,3] lowerTau = (55807 / 184318 : ℝ) + (1 / 184318 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_2_3]
  have harg : (3 : ℝ) + ((5116 / 16897 : ℝ) + (-1 / 16897 : ℝ) * Real.sqrt 3) = (55807 / 16897 : ℝ) + (-1 / 16897 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (55807 / 16897 : ℝ) (-1 / 16897 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1_3_3_3_3 : prefixEval [1,2,1,3,3,3,3] lowerTau = (44368 / 60397 : ℝ) + (-1 / 60397 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_3]
  have harg : (1 : ℝ) + ((11775 / 32593 : ℝ) + (1 / 32593 : ℝ) * Real.sqrt 3) = (44368 / 32593 : ℝ) + (1 / 32593 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (44368 / 32593 : ℝ) (1 / 32593 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_2_1_3 : prefixEval [1,3,1,2,2,1,3] lowerTau = (7483 / 9502 : ℝ) + (-1 / 9502 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_2_1_3]
  have harg : (1 : ℝ) + ((1590 / 5893 : ℝ) + (1 / 5893 : ℝ) * Real.sqrt 3) = (7483 / 5893 : ℝ) + (1 / 5893 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (7483 / 5893 : ℝ) (1 / 5893 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_2_2_3 : prefixEval [1,3,1,2,2,2,3] lowerTau = (14216 / 18049 : ℝ) + (-1 / 18049 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_2_2_3]
  have harg : (1 : ℝ) + ((3019 / 11197 : ℝ) + (1 / 11197 : ℝ) * Real.sqrt 3) = (14216 / 11197 : ℝ) + (1 / 11197 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (14216 / 11197 : ℝ) (1 / 11197 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_3_3_3_2_3 : prefixEval [1,3,3,3,3,2,3] lowerTau = (240125 / 312829 : ℝ) + (-1 / 312829 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_3_2_3]
  have harg : (1 : ℝ) + ((55807 / 184318 : ℝ) + (1 / 184318 : ℝ) * Real.sqrt 3) = (240125 / 184318 : ℝ) + (1 / 184318 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (240125 / 184318 : ℝ) (1 / 184318 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_3_3_3_3_3 : prefixEval [2,1,3,3,3,3,3] lowerTau = (128517 / 355678 : ℝ) + (-1 / 355678 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_3_3]
  have harg : (2 : ℝ) + ((11881 / 15479 : ℝ) + (1 / 46437 : ℝ) * Real.sqrt 3) = (42839 / 15479 : ℝ) + (1 / 46437 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (42839 / 15479 : ℝ) (1 / 46437 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_2_1_1_3 : prefixEval [3,1,2,2,1,1,3] lowerTau = (3959 / 14662 : ℝ) + (-1 / 14662 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_2_1_1_3]
  have harg : (3 : ℝ) + ((752 / 1069 : ℝ) + (1 / 1069 : ℝ) * Real.sqrt 3) = (3959 / 1069 : ℝ) + (1 / 1069 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3959 / 1069 : ℝ) (1 / 1069 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_2_2_2_1_3 : prefixEval [3,1,2,2,2,1,3] lowerTau = (9257 / 34318 : ℝ) + (-1 / 34318 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_2_2_2_1_3]
  have harg : (3 : ℝ) + ((1766 / 2497 : ℝ) + (1 / 2497 : ℝ) * Real.sqrt 3) = (9257 / 2497 : ℝ) + (1 / 2497 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (9257 / 2497 : ℝ) (1 / 2497 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_2_3 : prefixEval [3,1,3,1,2,2,3] lowerTau = (3955 / 14978 : ℝ) + (-1 / 44934 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_2_3]
  have harg : (3 : ℝ) + ((2466 / 3133 : ℝ) + (1 / 3133 : ℝ) * Real.sqrt 3) = (11865 / 3133 : ℝ) + (1 / 3133 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (11865 / 3133 : ℝ) (1 / 3133 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_3_3_3_3_1_1_3 : prefixEval [3,3,3,3,1,1,3] lowerTau = (68352 / 225733 : ℝ) + (-1 / 225733 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_1_1_3]
  have harg : (3 : ℝ) + ((2087 / 6899 : ℝ) + (1 / 20697 : ℝ) * Real.sqrt 3) = (22784 / 6899 : ℝ) + (1 / 20697 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (22784 / 6899 : ℝ) (1 / 20697 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_3_3_2_1_3 : prefixEval [3,3,3,3,2,1,3] lowerTau = (167754 / 554041 : ℝ) + (-1 / 554041 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_2_1_3]
  have harg : (3 : ℝ) + ((5125 / 16931 : ℝ) + (1 / 50793 : ℝ) * Real.sqrt 3) = (55918 / 16931 : ℝ) + (1 / 50793 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (55918 / 16931 : ℝ) (1 / 50793 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1_3_3_3_3_3 : prefixEval [1,2,1,3,3,3,3,3] lowerTau = (484195 / 659149 : ℝ) + (1 / 659149 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_3_3]
  have harg : (1 : ℝ) + ((128517 / 355678 : ℝ) + (-1 / 355678 : ℝ) * Real.sqrt 3) = (484195 / 355678 : ℝ) + (-1 / 355678 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (484195 / 355678 : ℝ) (-1 / 355678 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_2_1_1_3 : prefixEval [1,3,1,2,2,1,1,3] lowerTau = (6207 / 7883 : ℝ) + (1 / 23649 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_2_1_1_3]
  have harg : (1 : ℝ) + ((3959 / 14662 : ℝ) + (-1 / 14662 : ℝ) * Real.sqrt 3) = (18621 / 14662 : ℝ) + (-1 / 14662 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (18621 / 14662 : ℝ) (-1 / 14662 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_2_2_2_1_3 : prefixEval [1,3,1,2,2,2,1,3] lowerTau = (14525 / 18443 : ℝ) + (1 / 55329 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_2_2_2_1_3]
  have harg : (1 : ℝ) + ((9257 / 34318 : ℝ) + (-1 / 34318 : ℝ) * Real.sqrt 3) = (43575 / 34318 : ℝ) + (-1 / 34318 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (43575 / 34318 : ℝ) (-1 / 34318 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_2_3 : prefixEval [1,3,1,3,1,2,2,3] lowerTau = (56799 / 71797 : ℝ) + (1 / 71797 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_2_3]
  have harg : (1 : ℝ) + ((3955 / 14978 : ℝ) + (-1 / 44934 : ℝ) * Real.sqrt 3) = (18933 / 14978 : ℝ) + (-1 / 44934 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (18933 / 14978 : ℝ) (-1 / 44934 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_3_3_3_3_1_1_3 : prefixEval [1,3,3,3,3,1,1,3] lowerTau = (294085 / 383134 : ℝ) + (1 / 383134 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_3_1_1_3]
  have harg : (1 : ℝ) + ((68352 / 225733 : ℝ) + (-1 / 225733 : ℝ) * Real.sqrt 3) = (294085 / 225733 : ℝ) + (-1 / 225733 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (294085 / 225733 : ℝ) (-1 / 225733 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3_3_2_1_3 : prefixEval [1,3,3,3,3,2,1,3] lowerTau = (721795 / 940342 : ℝ) + (1 / 940342 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_3_2_1_3]
  have harg : (1 : ℝ) + ((167754 / 554041 : ℝ) + (-1 / 554041 : ℝ) * Real.sqrt 3) = (721795 / 554041 : ℝ) + (-1 / 554041 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (721795 / 554041 : ℝ) (-1 / 554041 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_3_3_3_3_2_3 : prefixEval [2,1,3,3,3,3,2,3] lowerTau = (865783 / 2396134 : ℝ) + (1 / 2396134 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_3_2_3]
  have harg : (2 : ℝ) + ((240125 / 312829 : ℝ) + (-1 / 312829 : ℝ) * Real.sqrt 3) = (865783 / 312829 : ℝ) + (-1 / 312829 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (865783 / 312829 : ℝ) (-1 / 312829 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_2_1_3 : prefixEval [3,1,3,1,2,2,1,3] lowerTau = (35989 / 136309 : ℝ) + (1 / 136309 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_2_1_3]
  have harg : (3 : ℝ) + ((7483 / 9502 : ℝ) + (-1 / 9502 : ℝ) * Real.sqrt 3) = (35989 / 9502 : ℝ) + (-1 / 9502 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (35989 / 9502 : ℝ) (-1 / 9502 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_2_2_3 : prefixEval [3,1,3,1,2,2,2,3] lowerTau = (68363 / 258934 : ℝ) + (1 / 258934 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_2_2_3]
  have harg : (3 : ℝ) + ((14216 / 18049 : ℝ) + (-1 / 18049 : ℝ) * Real.sqrt 3) = (68363 / 18049 : ℝ) + (-1 / 18049 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (68363 / 18049 : ℝ) (-1 / 18049 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_3_3_3_1_2_1_3 : prefixEval [3,3,3,3,1,2,1,3] lowerTau = (388099 / 1281694 : ℝ) + (1 / 1281694 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_1_2_1_3]
  have harg : (3 : ℝ) + ((35548 / 117517 : ℝ) + (-1 / 117517 : ℝ) * Real.sqrt 3) = (388099 / 117517 : ℝ) + (-1 / 117517 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (388099 / 117517 : ℝ) (-1 / 117517 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1_3_3_3_3_2_3 : prefixEval [1,2,1,3,3,3,3,2,3] lowerTau = (3261917 / 4440529 : ℝ) + (-1 / 4440529 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_3_2_3]
  have harg : (1 : ℝ) + ((865783 / 2396134 : ℝ) + (1 / 2396134 : ℝ) * Real.sqrt 3) = (3261917 / 2396134 : ℝ) + (1 / 2396134 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3261917 / 2396134 : ℝ) (1 / 2396134 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_2_1_3 : prefixEval [1,3,1,3,1,2,2,1,3] lowerTau = (172298 / 217789 : ℝ) + (-1 / 217789 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_2_1_3]
  have harg : (1 : ℝ) + ((35989 / 136309 : ℝ) + (1 / 136309 : ℝ) * Real.sqrt 3) = (172298 / 136309 : ℝ) + (1 / 136309 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (172298 / 136309 : ℝ) (1 / 136309 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_2_2_3 : prefixEval [1,3,1,3,1,2,2,2,3] lowerTau = (109099 / 137903 : ℝ) + (-1 / 413709 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_2_2_3]
  have harg : (1 : ℝ) + ((68363 / 258934 : ℝ) + (1 / 258934 : ℝ) * Real.sqrt 3) = (327297 / 258934 : ℝ) + (1 / 258934 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (327297 / 258934 : ℝ) (1 / 258934 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_3_3_3_1_2_1_3 : prefixEval [1,3,3,3,3,1,2,1,3] lowerTau = (1669793 / 2175409 : ℝ) + (-1 / 2175409 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_3_3_3_1_2_1_3]
  have harg : (1 : ℝ) + ((388099 / 1281694 : ℝ) + (1 / 1281694 : ℝ) * Real.sqrt 3) = (1669793 / 1281694 : ℝ) + (1 / 1281694 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1669793 / 1281694 : ℝ) (1 / 1281694 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_3_1_3_1_2_2_3 : prefixEval [2,1,3,1,3,1,2,2,3] lowerTau = (200393 / 559318 : ℝ) + (-1 / 559318 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_2_3]
  have harg : (2 : ℝ) + ((56799 / 71797 : ℝ) + (1 / 71797 : ℝ) * Real.sqrt 3) = (200393 / 71797 : ℝ) + (1 / 71797 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (200393 / 71797 : ℝ) (1 / 71797 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_3_3_3_3_1_1_3 : prefixEval [2,1,3,3,3,3,1,1,3] lowerTau = (353451 / 978203 : ℝ) + (-1 / 2934609 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_3_1_1_3]
  have harg : (2 : ℝ) + ((294085 / 383134 : ℝ) + (1 / 383134 : ℝ) * Real.sqrt 3) = (1060353 / 383134 : ℝ) + (1 / 383134 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1060353 / 383134 : ℝ) (1 / 383134 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3_3_2_1_3 : prefixEval [2,1,3,3,3,3,2,1,3] lowerTau = (867493 / 2400863 : ℝ) + (-1 / 7202589 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_3_2_1_3]
  have harg : (2 : ℝ) + ((721795 / 940342 : ℝ) + (1 / 940342 : ℝ) * Real.sqrt 3) = (2602479 / 940342 : ℝ) + (1 / 940342 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2602479 / 940342 : ℝ) (1 / 940342 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_2_1_1_3 : prefixEval [3,1,3,1,2,2,1,1,3] lowerTau = (89568 / 339229 : ℝ) + (-1 / 339229 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_2_1_1_3]
  have harg : (3 : ℝ) + ((6207 / 7883 : ℝ) + (1 / 23649 : ℝ) * Real.sqrt 3) = (29856 / 7883 : ℝ) + (1 / 23649 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (29856 / 7883 : ℝ) (1 / 23649 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_3_1_3_1_2_2_2_1_3 : prefixEval [3,1,3,1,2,2,2,1,3] lowerTau = (209562 / 793729 : ℝ) + (-1 / 793729 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_2_2_2_1_3]
  have harg : (3 : ℝ) + ((14525 / 18443 : ℝ) + (1 / 55329 : ℝ) * Real.sqrt 3) = (69854 / 18443 : ℝ) + (1 / 55329 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (69854 / 18443 : ℝ) (1 / 55329 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_3 : prefixEval [1,2,1,3,1,3,1,2,2,3] lowerTau = (253237 / 343967 : ℝ) + (1 / 1031901 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_2_3]
  have harg : (1 : ℝ) + ((200393 / 559318 : ℝ) + (-1 / 559318 : ℝ) * Real.sqrt 3) = (759711 / 559318 : ℝ) + (-1 / 559318 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (759711 / 559318 : ℝ) (-1 / 559318 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1_3_3_3_3_1_1_3 : prefixEval [1,2,1,3,3,3,3,1,1,3] lowerTau = (3994962 / 5438449 : ℝ) + (1 / 5438449 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_3_1_1_3]
  have harg : (1 : ℝ) + ((353451 / 978203 : ℝ) + (-1 / 2934609 : ℝ) * Real.sqrt 3) = (1331654 / 978203 : ℝ) + (-1 / 2934609 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1331654 / 978203 : ℝ) (-1 / 2934609 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3_3_2_1_3 : prefixEval [1,2,1,3,3,3,3,2,1,3] lowerTau = (9805068 / 13347889 : ℝ) + (1 / 13347889 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_3_2_1_3]
  have harg : (1 : ℝ) + ((867493 / 2400863 : ℝ) + (-1 / 7202589 : ℝ) * Real.sqrt 3) = (3268356 / 2400863 : ℝ) + (-1 / 7202589 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3268356 / 2400863 : ℝ) (-1 / 7202589 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_2_1_1_3 : prefixEval [1,3,1,3,1,2,2,1,1,3] lowerTau = (428797 / 542014 : ℝ) + (1 / 542014 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_2_1_1_3]
  have harg : (1 : ℝ) + ((89568 / 339229 : ℝ) + (-1 / 339229 : ℝ) * Real.sqrt 3) = (428797 / 339229 : ℝ) + (-1 / 339229 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (428797 / 339229 : ℝ) (-1 / 339229 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_3_1_3_1_2_2_2_1_3 : prefixEval [1,3,1,3,1,2,2,2,1,3] lowerTau = (1003291 / 1268182 : ℝ) + (1 / 1268182 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_3_1_3_1_2_2_2_1_3]
  have harg : (1 : ℝ) + ((209562 / 793729 : ℝ) + (-1 / 793729 : ℝ) * Real.sqrt 3) = (1003291 / 793729 : ℝ) + (-1 / 793729 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1003291 / 793729 : ℝ) (-1 / 793729 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_2_1_3_1_3_1_2_2_1_3 : prefixEval [2,1,3,1,3,1,2,2,1,3] lowerTau = (607876 / 1696657 : ℝ) + (1 / 1696657 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_2_1_3]
  have harg : (2 : ℝ) + ((172298 / 217789 : ℝ) + (-1 / 217789 : ℝ) * Real.sqrt 3) = (607876 / 217789 : ℝ) + (-1 / 217789 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (607876 / 217789 : ℝ) (-1 / 217789 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_2_2_3 : prefixEval [2,1,3,1,3,1,2,2,2,3] lowerTau = (1154715 / 3222958 : ℝ) + (1 / 3222958 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_2_2_3]
  have harg : (2 : ℝ) + ((109099 / 137903 : ℝ) + (-1 / 413709 : ℝ) * Real.sqrt 3) = (384905 / 137903 : ℝ) + (-1 / 413709 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (384905 / 137903 : ℝ) (-1 / 413709 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_3_3_3_1_2_1_3 : prefixEval [2,1,3,3,3,3,1,2,1,3] lowerTau = (6020611 / 16662502 : ℝ) + (1 / 16662502 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_3_3_3_1_2_1_3]
  have harg : (2 : ℝ) + ((1669793 / 2175409 : ℝ) + (-1 / 2175409 : ℝ) * Real.sqrt 3) = (6020611 / 2175409 : ℝ) + (-1 / 2175409 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (6020611 / 2175409 : ℝ) (-1 / 2175409 : ℝ) (by norm_num)]
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

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_1_3 : prefixEval [1,2,1,3,1,3,1,2,2,1,3] lowerTau = (2304533 / 3130198 : ℝ) + (-1 / 3130198 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_2_1_3]
  have harg : (1 : ℝ) + ((607876 / 1696657 : ℝ) + (1 / 1696657 : ℝ) * Real.sqrt 3) = (2304533 / 1696657 : ℝ) + (1 / 1696657 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2304533 / 1696657 : ℝ) (1 / 1696657 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_2_3 : prefixEval [1,2,1,3,1,3,1,2,2,2,3] lowerTau = (4377673 / 5946097 : ℝ) + (-1 / 5946097 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_2_2_3]
  have harg : (1 : ℝ) + ((1154715 / 3222958 : ℝ) + (1 / 3222958 : ℝ) * Real.sqrt 3) = (4377673 / 3222958 : ℝ) + (1 / 3222958 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (4377673 / 3222958 : ℝ) (1 / 3222958 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_3_3_3_1_2_1_3 : prefixEval [1,2,1,3,3,3,3,1,2,1,3] lowerTau = (22683113 / 30879133 : ℝ) + (-1 / 30879133 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_3_3_3_1_2_1_3]
  have harg : (1 : ℝ) + ((6020611 / 16662502 : ℝ) + (1 / 16662502 : ℝ) * Real.sqrt 3) = (22683113 / 16662502 : ℝ) + (1 / 16662502 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (22683113 / 16662502 : ℝ) (1 / 16662502 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_2_1_1_3 : prefixEval [2,1,3,1,3,1,2,2,1,1,3] lowerTau = (504275 / 1407491 : ℝ) + (-1 / 4222473 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_2_1_1_3]
  have harg : (2 : ℝ) + ((428797 / 542014 : ℝ) + (1 / 542014 : ℝ) * Real.sqrt 3) = (1512825 / 542014 : ℝ) + (1 / 542014 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1512825 / 542014 : ℝ) (1 / 542014 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_2_1_3_1_3_1_2_2_2_1_3 : prefixEval [2,1,3,1,3,1,2,2,2,1,3] lowerTau = (1179885 / 3293207 : ℝ) + (-1 / 9879621 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_1_3_1_3_1_2_2_2_1_3]
  have harg : (2 : ℝ) + ((1003291 / 1268182 : ℝ) + (1 / 1268182 : ℝ) * Real.sqrt 3) = (3539655 / 1268182 : ℝ) + (1 / 1268182 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3539655 / 1268182 : ℝ) (1 / 1268182 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_1_1_3 : prefixEval [1,2,1,3,1,3,1,2,2,1,1,3] lowerTau = (5735298 / 7790137 : ℝ) + (1 / 7790137 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_2_1_1_3]
  have harg : (1 : ℝ) + ((504275 / 1407491 : ℝ) + (-1 / 4222473 : ℝ) * Real.sqrt 3) = (1911766 / 1407491 : ℝ) + (-1 / 4222473 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1911766 / 1407491 : ℝ) (-1 / 4222473 : ℝ) (by norm_num)]
  norm_num
  ring

@[simp] private theorem bp_1_2_1_3_1_3_1_2_2_2_1_3 : prefixEval [1,2,1,3,1,3,1,2,2,2,1,3] lowerTau = (13419276 / 18227113 : ℝ) + (1 / 18227113 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [bp_2_1_3_1_3_1_2_2_2_1_3]
  have harg : (1 : ℝ) + ((1179885 / 3293207 : ℝ) + (-1 / 9879621 : ℝ) * Real.sqrt 3) = (4473092 / 3293207 : ℝ) + (-1 / 9879621 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (4473092 / 3293207 : ℝ) (-1 / 9879621 : ℝ) (by norm_num)]
  norm_num
  ring

theorem solution :
  (prefixEval [] lowerTau = (-1 : ℝ) + 1 * Real.sqrt 3) ∧
  (prefixEval [3] lowerTau = (2 : ℝ) + (-1 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [2,3] lowerTau = (4 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [3,3] lowerTau = (5 / 22 : ℝ) + (1 / 22 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,1,3] lowerTau = (9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3] lowerTau = (52 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3] lowerTau = (355 / 481 : ℝ) + (-1 / 481 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,2,1,3] lowerTau = (735 / 1006 : ℝ) + (1 / 1006 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,2,3] lowerTau = (2513 / 3421 : ℝ) + (1 / 3421 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3] lowerTau = (4087 / 5566 : ℝ) + (1 / 5566 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,1,3] lowerTau = (1006 / 1367 : ℝ) + (-1 / 4101 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,2,1,3] lowerTau = (2504 / 3407 : ℝ) + (-1 / 10221 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,2,3] lowerTau = (27413 / 37318 : ℝ) + (-1 / 37318 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3] lowerTau = (44368 / 60397 : ℝ) + (-1 / 60397 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,2,1,3] lowerTau = (17117 / 23257 : ℝ) + (1 / 23257 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,1,1,3] lowerTau = (33633 / 45793 : ℝ) + (1 / 45793 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,2,1,3] lowerTau = (82443 / 112237 : ℝ) + (1 / 112237 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,2,3] lowerTau = (299030 / 407077 : ℝ) + (1 / 407077 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,3] lowerTau = (484195 / 659149 : ℝ) + (1 / 659149 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,1,2,1,3] lowerTau = (190985 / 260038 : ℝ) + (-1 / 260038 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,1,1,3] lowerTau = (122055 / 166154 : ℝ) + (-1 / 498462 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,2,1,3] lowerTau = (299605 / 407858 : ℝ) + (-1 / 1223574 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,2,3] lowerTau = (3261917 / 4440529 : ℝ) + (-1 / 4440529 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,2,1,3,1,3,2,3] lowerTau = (804501 / 1098526 : ℝ) + (1 / 1098526 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,3] lowerTau = (253237 / 343967 : ℝ) + (1 / 1031901 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,1,2,1,3] lowerTau = (2079038 / 2830201 : ℝ) + (1 / 2830201 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,1,1,3] lowerTau = (3994962 / 5438449 : ℝ) + (1 / 5438449 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,2,1,3] lowerTau = (9805068 / 13347889 : ℝ) + (1 / 13347889 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,2,1,3,1,3,2,1,3] lowerTau = (2402518 / 3280573 : ℝ) + (-1 / 3280573 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,1,3] lowerTau = (2304533 / 3130198 : ℝ) + (-1 / 3130198 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,2,3] lowerTau = (4377673 / 5946097 : ℝ) + (-1 / 5946097 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,1,2,1,3] lowerTau = (22683113 / 30879133 : ℝ) + (-1 / 30879133 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,1,1,3] lowerTau = (5735298 / 7790137 : ℝ) + (1 / 7790137 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,2,1,3] lowerTau = (13419276 / 18227113 : ℝ) + (1 / 18227113 : ℝ) * Real.sqrt 3) := by
  exact ⟨bp_nil, bp_3, bp_2_3, bp_3_3, bp_1_1_3, bp_1_2_1_3, bp_1_2_1_3_3, bp_1_2_1_2_1_3, bp_1_2_1_3_2_3, bp_1_2_1_3_3_3, bp_1_2_1_3_1_1_3, bp_1_2_1_3_2_1_3, bp_1_2_1_3_3_2_3, bp_1_2_1_3_3_3_3, bp_1_2_1_3_1_2_1_3, bp_1_2_1_3_3_1_1_3, bp_1_2_1_3_3_2_1_3, bp_1_2_1_3_3_3_2_3, bp_1_2_1_3_3_3_3_3, bp_1_2_1_3_3_1_2_1_3, bp_1_2_1_3_3_3_1_1_3, bp_1_2_1_3_3_3_2_1_3, bp_1_2_1_3_3_3_3_2_3, bp_1_2_1_2_1_3_1_3_2_3, bp_1_2_1_3_1_3_1_2_2_3, bp_1_2_1_3_3_3_1_2_1_3, bp_1_2_1_3_3_3_3_1_1_3, bp_1_2_1_3_3_3_3_2_1_3, bp_1_2_1_2_1_3_1_3_2_1_3, bp_1_2_1_3_1_3_1_2_2_1_3, bp_1_2_1_3_1_3_1_2_2_2_3, bp_1_2_1_3_3_3_3_1_2_1_3, bp_1_2_1_3_1_3_1_2_2_1_1_3, bp_1_2_1_3_1_3_1_2_2_2_1_3⟩
#print axioms solution
