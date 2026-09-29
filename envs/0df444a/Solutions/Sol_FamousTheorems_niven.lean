-- Prove2me | solution 1 for FamousTheorems.niven
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T06:56:38.373643+00:00
-- url     : https://prove2.me/submissions/bc812b84-1fad-47b4-86b4-1fcde1826944

import Mathlib

open Filter Set Topology

theorem solution {θ : ℝ} (hθ : ∃ r : ℚ, θ = r * Real.pi) (hcos : ∃ q : ℚ, Real.cos θ = q) :
    Real.cos θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := _root_.niven hθ hcos
