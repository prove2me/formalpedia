-- Prove2me | solution 1 for FamousTheorems.image_icc
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:54.790152+00:00
-- url     : https://prove2.me/submissions/b2a6279c-6a70-4810-a7c1-db4e62c14873

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} [inst : ConditionallyCompleteLinearOrder α] 
    [inst_1 : TopologicalSpace α] [OrderTopology α] [inst_3 : TopologicalSpace β] [DenselyOrdered α] 
    [inst_5 : ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β} {a b : α}, 
    a ≤ b → ContinuousOn f (Icc a b) → f '' Icc a b = Icc (sInf (f '' Icc a b)) (sSup (f '' Icc a b)) :=
  @_root_.ContinuousOn.image_Icc
