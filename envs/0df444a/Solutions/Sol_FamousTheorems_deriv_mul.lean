-- Prove2me | solution 1 for FamousTheorems.deriv_mul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:11.485617+00:00
-- url     : https://prove2.me/submissions/bc23785e-13c2-44df-8576-10fd0038f388

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {𝔸 : Type u_2} [inst_1 : NormedRing 𝔸] 
    [inst_2 : NormedAlgebra 𝕜 𝔸] {c d : 𝕜 → 𝔸}, 
    DifferentiableAt 𝕜 c x → DifferentiableAt 𝕜 d x → deriv (c * d) x = deriv c x * d x + c x * deriv d x :=
  @_root_.deriv_mul
