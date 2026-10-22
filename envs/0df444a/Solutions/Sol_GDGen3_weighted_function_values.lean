-- Prove2me | solution 1 for GDGen3.weighted_function_values
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:06:17.651441+00:00
-- url     : https://prove2.me/submissions/ed540e36-a5f1-4e9d-9f81-3381f0abc6be

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (L : ℕ → ℕ → ℝ) (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * (f i - f j)) =
      ∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j - L j i)) * f i := by
  simp only [sum_sub_distrib, sum_mul, sub_mul, mul_sub]
  congr 1
  rw [sum_comm]
