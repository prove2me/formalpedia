-- Prove2me | solution 1 for FamousTheorems.multipliable_iff_cauchyseq_finset
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:55:22.171881+00:00
-- url     : https://prove2.me/submissions/ad817085-fe92-4d9e-be93-c8fd17ae3cb2

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] [inst_1 : CommMonoid α] 
    [CompleteSpace α] {f : β → α}, Multipliable f ↔ CauchySeq fun s => ∏ b ∈ s, f b :=
  @_root_.multipliable_iff_cauchySeq_finset
