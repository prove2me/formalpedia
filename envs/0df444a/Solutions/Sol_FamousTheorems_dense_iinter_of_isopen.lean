-- Prove2me | solution 1 for FamousTheorems.dense_iinter_of_isopen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:04.793676+00:00
-- url     : https://prove2.me/submissions/b4f8e6a8-658e-4d5d-8751-eec1321ca924

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {X : Type u_1} {ι : Sort u_2} [inst : TopologicalSpace X] [BaireSpace X] [Countable ι] 
    {f : ι → Set X}, (∀ (i : ι), IsOpen (f i)) → (∀ (i : ι), Dense (f i)) → Dense (⋂ s, f s) :=
  @_root_.dense_iInter_of_isOpen
