-- Prove2me | solution 1 for GDGen3.small_step_identity
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:47:43.77298+00:00
-- url     : https://prove2.me/submissions/d9e96a63-4bc7-453b-96d4-f81e272bba44

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_small_step_identity

lemma symmetric_square_telescope (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) (N : ℕ) :
    2 * (∑ i ∈ range N, ∑ j ∈ range i, P i j) + (∑ i ∈ range N, P i i) =
      ∑ i ∈ range N, ∑ j ∈ range N, P i j := by
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ, sum_add_distrib]
    have he : (∑ i ∈ range n, P i n) = ∑ i ∈ range n, P n i := by
      apply sum_congr rfl; intro i hi; exact hP i n
    rw [he]
    linear_combination ih

end GDGen3Proof_small_step_identity

open GDGen3Proof_small_step_identity

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
