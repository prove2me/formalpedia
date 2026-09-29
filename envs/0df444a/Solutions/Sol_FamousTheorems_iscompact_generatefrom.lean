-- Prove2me | solution 1 for FamousTheorems.iscompact_generatefrom
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:55:13.666933+00:00
-- url     : https://prove2.me/submissions/ffd070a0-f04c-4ac6-bcc2-773eb08d948d

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {X : Type u_1} [T : TopologicalSpace X] {S : Set (Set X)}, 
    T = TopologicalSpace.generateFrom S → ∀ {s : Set X}, (∀ P ⊆ S, s ⊆ ⋃₀ P → ∃ Q ⊆ P, Q.Finite ∧ s ⊆ ⋃₀ Q) → IsCompact s :=
  @_root_.isCompact_generateFrom
