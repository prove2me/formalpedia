-- Prove2me | solution 1 for FamousTheorems.eventually_eq_zero_or_eventually_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:11.434576+00:00
-- url     : https://prove2.me/submissions/31a26fff-7b46-4a90-83dc-f8eadbe8a73c

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
    {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {z₀ : 𝕜}, 
    AnalyticAt 𝕜 f z₀ → (∀ᶠ (z : 𝕜) in 𝓝 z₀, f z = 0) ∨ ∀ᶠ (z : 𝕜) in 𝓝[≠] z₀, f z ≠ 0 :=
  @_root_.AnalyticAt.eventually_eq_zero_or_eventually_ne_zero
