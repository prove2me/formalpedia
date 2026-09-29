-- Prove2me | solution 1 for FamousTheorems.card_sylow_modeq_one
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:34.163973+00:00
-- url     : https://prove2.me/submissions/bcd95f47-a970-417c-b4dc-eb56bcc9da9e

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ (p : ℕ) (G : Type u_1) [inst : Group G] [Fact (Nat.Prime p)] [Finite (Sylow p G)], 
    Nat.card (Sylow p G) ≡ 1 [MOD p] :=
  @_root_.card_sylow_modEq_one
