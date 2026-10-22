-- Prove2me | solution 2 for GDGen3.small_step_identity
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:41:47.242762+00:00
-- url     : https://prove2.me/submissions/e57d184c-a78a-456e-998f-306c1a82a3a1

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_symmetric_square_telescope

noncomputable section

open Finset

open GDGen3

theorem solution (N : ℕ) (h : ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ)
    (X0 XN : ℝ) (hP : ∀ i j, P i j = P j i)
    (htrajectory : XN = X0 - 2 * h * (∑ i ∈ range N, R i)
      + h ^ 2 * (∑ i ∈ range N, ∑ j ∈ range N, P i j)) :
    h * smallK N h f (fun i => P i i)
      + 2 * h * (∑ i ∈ range N, (-f i + gself h R P i - (1 / 2) * P i i)) =
      X0 - XN - 2 * (N : ℝ) * h * f N - (N : ℝ) * h * (1 + (N : ℝ) * h) * P N N := by
  rw [htrajectory]
  unfold smallK gself
  simp only [sum_sub_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum,
    sum_const, card_range, nsmul_eq_mul]
  have hs := symmetric_square_telescope P hP N
  linear_combination -h ^ 2 * hs
