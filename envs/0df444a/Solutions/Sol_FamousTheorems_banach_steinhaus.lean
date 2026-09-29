-- Prove2me | solution 1 for FamousTheorems.banach_steinhaus
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T06:56:21.909726+00:00
-- url     : https://prove2.me/submissions/c24a3b57-ad09-47d9-b8cb-85554d327291

import Mathlib

open Filter Set Topology

theorem solution {E F 𝕜 𝕜₂ : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
    {ι : Type*} [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C' :=
  _root_.banach_steinhaus h
