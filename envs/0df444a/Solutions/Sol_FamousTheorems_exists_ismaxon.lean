-- Prove2me | solution 1 for FamousTheorems.exists_ismaxon
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:55:13.750916+00:00
-- url     : https://prove2.me/submissions/fbab2e4b-eb2f-4c71-84dd-e7ddeee7aa82

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : TopologicalSpace α] 
    [inst_2 : TopologicalSpace β] [ClosedIciTopology α] {s : Set β}, 
    IsCompact s → s.Nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, IsMaxOn f s x :=
  @_root_.IsCompact.exists_isMaxOn
