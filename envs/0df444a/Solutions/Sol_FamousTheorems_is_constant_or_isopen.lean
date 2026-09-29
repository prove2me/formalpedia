-- Prove2me | solution 1 for FamousTheorems.is_constant_or_isopen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:02:02.094007+00:00
-- url     : https://prove2.me/submissions/1e879051-d669-49ab-bd5c-39e6df73c7ea

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
    {U : Set E} {g : E → ℂ}, 
    AnalyticOnNhd ℂ g U → IsPreconnected U → (∃ w, ∀ z ∈ U, g z = w) ∨ ∀ s ⊆ U, IsOpen s → IsOpen (g '' s) :=
  @_root_.AnalyticOnNhd.is_constant_or_isOpen
