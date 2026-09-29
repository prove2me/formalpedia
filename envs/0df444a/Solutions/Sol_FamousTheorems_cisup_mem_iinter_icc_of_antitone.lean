-- Prove2me | solution 1 for FamousTheorems.cisup_mem_iinter_icc_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:54:57.210009+00:00
-- url     : https://prove2.me/submissions/3fc917a7-f68f-477d-87f3-1ea6d92048c8

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} 
    [inst : ConditionallyCompletePartialOrderSup α] [inst_1 : Preorder β] [IsDirectedOrder β] {f g : β → α}, 
    Monotone f → Antitone g → f ≤ g → ⨆ n, f n ∈ ⋂ n, Icc (f n) (g n) :=
  @_root_.Monotone.ciSup_mem_iInter_Icc_of_antitone
