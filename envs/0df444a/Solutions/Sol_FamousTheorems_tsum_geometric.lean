-- Prove2me | solution 1 for FamousTheorems.tsum_geometric
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:15:02.377556+00:00
-- url     : https://prove2.me/submissions/352da70f-b9c6-4c80-9a5c-12d88b770850

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {K : Type*} [NormedDivisionRing K] [CompleteSpace K] {ξ : K}
    (h : ‖ξ‖ < 1) : ∑' n : ℕ, ξ ^ n = (1 - ξ)⁻¹ := tsum_geometric_of_norm_lt_one h
