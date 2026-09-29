-- Prove2me | solution 1 for FamousTheorems.hindman
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:15:55.740157+00:00
-- url     : https://prove2.me/submissions/94fd5b4f-f9d8-4424-9ad8-e89249dea3a7

import Mathlib

theorem solution {M : Type*} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (hs : s.Finite)
    (hcov : Hindman.FP a ⊆ ⋃₀ s) :
    ∃ c ∈ s, ∃ b : Stream' M, Hindman.FP b ⊆ c :=
  Hindman.FP_partition_regular a s hs hcov
