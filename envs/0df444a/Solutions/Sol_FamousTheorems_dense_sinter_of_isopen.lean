-- Prove2me | solution 1 for FamousTheorems.dense_sinter_of_isopen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:02:18.598272+00:00
-- url     : https://prove2.me/submissions/779cf8f3-0c52-4b5e-8ba2-66f74f935656

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {X : Type u_1} [inst : TopologicalSpace X] [BaireSpace X] {S : Set (Set X)}, 
    (∀ s ∈ S, IsOpen s) → S.Countable → (∀ s ∈ S, Dense s) → Dense (⋂₀ S) :=
  @_root_.dense_sInter_of_isOpen
