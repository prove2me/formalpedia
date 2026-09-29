-- Prove2me | solution 1 for FamousTheorems.uniformcontinuous_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:46.567178+00:00
-- url     : https://prove2.me/submissions/c37b738d-0ace-4a36-994b-e13349688ef8

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] 
    [inst_1 : UniformSpace β] [CompactSpace α] {f : α → β}, Continuous f → UniformContinuous f :=
  @_root_.CompactSpace.uniformContinuous_of_continuous
