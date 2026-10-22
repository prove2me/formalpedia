-- Prove2me | solution 1 for AvramDividend.Classical.chat06_arrival_prefix_reconstructs_past_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T17:40:37.445425+00:00
-- url     : https://prove2.me/submissions/429405dc-a441-4c6f-929f-5e6ed604d3b5

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


/-- On a fixed-horizon count cylinder, every earlier count is
reconstructed by finite threshold comparisons against the
observed prefix of interarrival times. -/
theorem solution
    (τ : ℕ → ℝ) (Z : ℕ → ℝ) (N : ℝ → ℕ)
    (horizon : ℝ) (s : ℝ) (hs : s ≤ horizon) (n : ℕ)
    (hClock : N horizon = n)
    (hThreshold : ∀ u : ℝ, ∀ k : ℕ,
      k < N u ↔
        (∑ i ∈ Finset.range (k + 1), τ i) ≤ u)
    (hZ : ∀ i, Z i = if i < n then τ i else 0) :
    ((Finset.range n).filter (fun k =>
      (∑ i ∈ Finset.range (k + 1), Z i) ≤ s)).card = N s := by
  have hBound : N s ≤ n := by
    by_contra hn
    have hgt : n < N s := Nat.lt_of_not_ge hn
    have he : (∑ i ∈ Finset.range (n + 1), τ i) ≤ s :=
      (hThreshold s n).mp hgt
    have hc : n < N horizon :=
      (hThreshold horizon n).mpr (le_trans he hs)
    exact Nat.lt_irrefl n (hClock ▸ hc)
  have hSum (k : ℕ) (hk : k < n) :
      (∑ i ∈ Finset.range (k + 1), Z i) =
        (∑ i ∈ Finset.range (k + 1), τ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hin : i < n := lt_of_le_of_lt hik hk
    simp [hZ, hin]
  have hEq :
      (Finset.range n).filter (fun k =>
        (∑ i ∈ Finset.range (k + 1), Z i) ≤ s) =
      Finset.range (N s) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hk, hsk⟩
      exact (hThreshold s k).mpr ((hSum k hk) ▸ hsk)
    · intro hk
      have hkn : k < n := lt_of_lt_of_le hk hBound
      exact ⟨hkn, by rw [hSum k hkn]; exact (hThreshold s k).mp hk⟩
  rw [hEq, Finset.card_range]
