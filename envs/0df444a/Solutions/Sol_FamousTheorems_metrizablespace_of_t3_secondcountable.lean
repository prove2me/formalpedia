-- Prove2me | solution 1 for FamousTheorems.metrizablespace_of_t3_secondcountable
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:05.403985+00:00
-- url     : https://prove2.me/submissions/c4b7db18-af5f-4b6b-90da-b20fb9d84482

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ (X : Type u_1) [inst : TopologicalSpace X] [T3Space X] 
    [SecondCountableTopology X], TopologicalSpace.MetrizableSpace X :=
  @_root_.TopologicalSpace.metrizableSpace_of_t3_secondCountable
