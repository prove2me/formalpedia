-- Prove2me | solution 1 for FamousTheorems.lucas_lehmer_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:33.972863+00:00
-- url     : https://prove2.me/submissions/7df53012-392a-4474-904f-288bc5fd144d

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ (p : ℕ), 1 < p → LucasLehmerTest p → Nat.Prime (mersenne p) :=
  @_root_.lucas_lehmer_sufficiency
