-- Prove2me | solution 1 for FamousTheorems.exists_list_transvec_mul_mul_list_transvec_eq_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:38.223448+00:00
-- url     : https://prove2.me/submissions/b8b6a13c-2a9b-4cab-a433-f8d03746c7c8

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {n : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] 
    [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n 𝕜), 
    ∃ L L' D, 
    (List.map Matrix.TransvectionStruct.toMatrix L).prod * M * (List.map Matrix.TransvectionStruct.toMatrix L').prod = 
    Matrix.diagonal D :=
  @_root_.Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal
