-- Prove2me | solution 1 for AvramDividend.Classical.chat06_random_index_future_arrival_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:49:34.694098+00:00
-- url     : https://prove2.me/submissions/8dc3486e-f814-4edf-9b5c-a8c57c3be4a8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- At a randomly selected renewal index, every later arrival
relative to a deterministic clock is the remaining current wait
plus the sum of the subsequent complete waiting times. -/
theorem solution
    {Ω : Type*} (τ : ℕ → Ω → ℝ)
    (N : Ω → ℕ) (clock : ℝ) (ω : Ω) (k : ℕ) :
    (∑ i ∈ Finset.range (N ω + 1 + k), τ i ω) - clock =
      (τ (N ω) ω -
        (clock - ∑ i ∈ Finset.range (N ω), τ i ω)) +
      ∑ j ∈ Finset.range k, τ (N ω + 1 + j) ω := by
  have hAdd :
      (∑ i ∈ Finset.range (N ω + 1 + k), τ i ω) =
        (∑ i ∈ Finset.range (N ω + 1), τ i ω) +
        ∑ j ∈ Finset.range k, τ (N ω + 1 + j) ω := by
    exact Finset.sum_range_add (fun i => τ i ω) (N ω + 1) k
  have hSucc :
      (∑ i ∈ Finset.range (N ω + 1), τ i ω) =
        (∑ i ∈ Finset.range (N ω), τ i ω) + τ (N ω) ω :=
    Finset.sum_range_succ (fun i => τ i ω) (N ω)
  rw [hAdd, hSucc]
  ring
