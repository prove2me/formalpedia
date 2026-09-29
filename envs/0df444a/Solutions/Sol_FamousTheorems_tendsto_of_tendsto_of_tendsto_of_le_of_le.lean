-- Prove2me | solution 1 for FamousTheorems.tendsto_of_tendsto_of_tendsto_of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:05.232512+00:00
-- url     : https://prove2.me/submissions/8ee79fbf-109d-4367-bac1-d7d124ee3fc8

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} [ts : TopologicalSpace α] 
    [inst : Preorder α] [OrderTopology α] {f g h : β → α} {b : Filter β} {a : α}, 
    Tendsto g b (𝓝 a) → 
    Tendsto h b (𝓝 a) → (∀ᶠ (b : β) in b, g b ≤ f b) → (∀ᶠ (b : β) in b, f b ≤ h b) → Tendsto f b (𝓝 a) :=
  @_root_.tendsto_of_tendsto_of_tendsto_of_le_of_le'
