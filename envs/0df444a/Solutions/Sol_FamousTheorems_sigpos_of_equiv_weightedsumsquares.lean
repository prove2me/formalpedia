-- Prove2me | solution 1 for FamousTheorems.sigpos_of_equiv_weightedsumsquares
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:46.472981+00:00
-- url     : https://prove2.me/submissions/18a839ce-2c30-447f-abb4-85c83ca1a518

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {M : Type u_1} [inst : AddCommGroup M] {𝕜 : Type u_2} 
    [inst_1 : Field 𝕜] [inst_2 : LinearOrder 𝕜] [inst_3 : Module 𝕜 M] {Q : QuadraticForm 𝕜 M} {ι : Type u_3} 
    [inst_4 : Fintype ι] {w : ι → 𝕜} [IsStrictOrderedRing 𝕜], 
    QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares 𝕜 w) → sigPos Q = {i | 0 < w i}.ncard :=
  @_root_.QuadraticForm.sigPos_of_equiv_weightedSumSquares
