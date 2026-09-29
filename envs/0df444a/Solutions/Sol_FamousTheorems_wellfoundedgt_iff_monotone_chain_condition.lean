-- Prove2me | solution 1 for FamousTheorems.wellfoundedgt_iff_monotone_chain_condition
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:54:31.936975+00:00
-- url     : https://prove2.me/submissions/1ed0a95c-a255-4e4d-8d03-60ef827d2022

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} [inst : Preorder α], 
    WellFoundedGT α ↔ ∀ (a : ℕ →o α), ∃ n, ∀ (m : ℕ), n ≤ m → ¬a n < a m :=
  @_root_.wellFoundedGT_iff_monotone_chain_condition'
