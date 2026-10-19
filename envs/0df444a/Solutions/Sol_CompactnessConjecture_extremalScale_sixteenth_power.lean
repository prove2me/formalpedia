-- Prove2me | solution 1 for CompactnessConjecture.extremalScale_sixteenth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/1692b824-9dfc-4639-a694-8dcea6e2f19d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Classical Topology
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (hn : 0 < n) :
    (extremalScale n) ^ 16 =
      (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold extremalScale
  calc
    ((n : ℝ) ^ ((4 : ℝ) / 3)) ^ 16 =
        (n : ℝ) ^ (((4 : ℝ) / 3) * (16 : ℝ)) := by
      exact (Real.rpow_mul_natCast hnreal.le
        ((4 : ℝ) / 3) 16).symm
    _ = (n : ℝ) ^ ((21 : ℝ) + (1 : ℝ) / 3) := by
      congr 1
      norm_num
    _ = (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      simp [Real.rpow_add hnreal]
end CompactnessConjecture
