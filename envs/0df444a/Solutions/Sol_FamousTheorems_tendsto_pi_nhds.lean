-- Prove2me | solution 1 for FamousTheorems.tendsto_pi_nhds
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:12.077228+00:00
-- url     : https://prove2.me/submissions/4e7ee810-077e-4531-8191-64899aba4af1

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {Y : Type u_1} {ι : Type u_2} {A : ι → Type u_3} [T : (i : ι) → TopologicalSpace (A i)] 
    {f : Y → (i : ι) → A i} {g : (i : ι) → A i} {u : Filter Y}, 
    Tendsto f u (𝓝 g) ↔ ∀ (x : ι), Tendsto (fun i => f i x) u (𝓝 (g x)) :=
  @_root_.tendsto_pi_nhds
