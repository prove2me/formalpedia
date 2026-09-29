-- Prove2me | solution 1 for FamousTheorems.exists_norm_nsmul_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:06.163318+00:00
-- url     : https://prove2.me/submissions/c70dbbbb-9c95-4a67-8f18-f16fdef7e560

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {T : ℝ} [hT : Fact (0 < T)] (ξ : AddCircle T) {n : ℕ}, 
    0 < n → ∃ j ∈ Icc 1 n, ‖j • ξ‖ ≤ T / ↑(n + 1) :=
  @_root_.AddCircle.exists_norm_nsmul_le
