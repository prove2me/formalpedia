-- Prove2me | solution 1 for FamousTheorems.erdos_kaplansky
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:23:22.232745+00:00
-- url     : https://prove2.me/submissions/2c7560f5-468e-4810-928e-618dad35832d

import Mathlib

theorem solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : Cardinal.aleph0 ≤ Module.rank K V) :
    Module.rank K (V →ₗ[K] K) = Cardinal.mk (V →ₗ[K] K) :=
  rank_dual_eq_card_dual_of_aleph0_le_rank h
