-- Prove2me | solution 1 for FamousTheorems.exists_maximal_of_chains_bounded
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:54:40.339224+00:00
-- url     : https://prove2.me/submissions/0711286a-9f2c-4d0a-8373-3e4b66e8bfae

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {r : α → α → Prop}, 
    (∀ (c : Set α), IsChain r c → ∃ ub, ∀ a ∈ c, r a ub) → 
    (∀ {a b c : α}, r a b → r b c → r a c) → ∃ m, ∀ (a : α), r m a → r a m :=
  @_root_.exists_maximal_of_chains_bounded
