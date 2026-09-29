-- Prove2me | solution 1 for FamousTheorems.deriv_comp
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:54.703973+00:00
-- url     : https://prove2.me/submissions/de5c7a02-5526-49b4-9bc6-ff19741e87ec

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] (x : 𝕜) {𝕜' : Type u_2} 
    [inst_1 : NontriviallyNormedField 𝕜'] [inst_2 : NormedAlgebra 𝕜 𝕜'] {h : 𝕜 → 𝕜'} {h₂ : 𝕜' → 𝕜'}, 
    DifferentiableAt 𝕜' h₂ (h x) → DifferentiableAt 𝕜 h x → deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
  @_root_.deriv_comp
