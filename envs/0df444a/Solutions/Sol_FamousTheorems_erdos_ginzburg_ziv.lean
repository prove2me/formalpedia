-- Prove2me | solution 1 for FamousTheorems.erdos_ginzburg_ziv
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:36.820611+00:00
-- url     : https://prove2.me/submissions/fce07ebf-6f92-44ec-9b18-b61f19425822

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {ι : Type u_1} {n : ℕ} {s : Finset ι} (a : ι → ZMod n), 
    2 * n - 1 ≤ s.card → ∃ t ⊆ s, t.card = n ∧ ∑ i ∈ t, a i = 0 :=
  @_root_.ZMod.erdos_ginzburg_ziv
