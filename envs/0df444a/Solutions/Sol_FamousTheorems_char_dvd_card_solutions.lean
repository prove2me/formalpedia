-- Prove2me | solution 1 for FamousTheorems.char_dvd_card_solutions
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:50.22888+00:00
-- url     : https://prove2.me/submissions/8cfcef21-f8de-45ac-a06a-29a3ff191630

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {K : Type u_1} {σ : Type u_2} [inst : Fintype K] [inst_1 : Field K] [inst_2 : Fintype σ] 
    [inst_3 : DecidableEq σ] [inst_4 : DecidableEq K] (p : ℕ) [CharP K p] {f : MvPolynomial σ K}, 
    f.totalDegree < Fintype.card σ → p ∣ Fintype.card { x // (MvPolynomial.eval x) f = 0 } :=
  @_root_.char_dvd_card_solutions
