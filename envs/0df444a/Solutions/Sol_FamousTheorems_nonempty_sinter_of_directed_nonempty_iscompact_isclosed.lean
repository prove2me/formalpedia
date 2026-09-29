-- Prove2me | solution 1 for FamousTheorems.nonempty_sinter_of_directed_nonempty_iscompact_isclosed
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:02:12.218809+00:00
-- url     : https://prove2.me/submissions/47d8add7-d333-4baf-b496-e59160d83718

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {X : Type u_1} [inst : TopologicalSpace X] 
    {S : Set (Set X)} [hS : Nonempty ↑S], 
    DirectedOn (fun x1 x2 => x1 ⊇ x2) S → 
    (∀ U ∈ S, U.Nonempty) → (∀ U ∈ S, IsCompact U) → (∀ U ∈ S, IsClosed U) → (⋂₀ S).Nonempty :=
  @_root_.IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
