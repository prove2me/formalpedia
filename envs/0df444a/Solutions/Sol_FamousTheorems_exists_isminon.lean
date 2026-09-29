-- Prove2me | solution 1 for FamousTheorems.exists_isminon
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:46.245328+00:00
-- url     : https://prove2.me/submissions/255de699-afec-4161-ad60-8308b3d5082c

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : TopologicalSpace α] 
    [inst_2 : TopologicalSpace β] [ClosedIicTopology α] {s : Set β}, 
    IsCompact s → s.Nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, IsMinOn f s x :=
  @_root_.IsCompact.exists_isMinOn
