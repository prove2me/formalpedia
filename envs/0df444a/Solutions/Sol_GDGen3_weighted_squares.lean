-- Prove2me | solution 1 for GDGen3.weighted_squares
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:09:33.302618+00:00
-- url     : https://prove2.me/submissions/e42c6a74-4df6-4be1-8059-d103ea8fa5ab

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (L P : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * (P i i + P j j)) =
      ∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j + L j i)) * P i i := by
  simp only [sum_add_distrib, sum_mul, add_mul, mul_add]
  congr 1
  rw [sum_comm]
