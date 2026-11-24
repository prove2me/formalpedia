-- Prove2me | solution 1 for DeletedPrimes.mertensSum_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:55:05.059061+00:00
-- url     : https://prove2.me/submissions/b6da808c-4424-4938-abcc-f4e4ea89911e

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) (α : ℝ) {a b : ℝ} (hab : a ≤ b) :
    mertensSum S α b - mertensSum S α a =
      ∑ p ∈ (Finset.Icc 1 ⌊b⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊a⌋₊).filter (· ∈ S),
        Real.log p / (p : ℝ) ^ α := by
  have hsub : (Finset.Icc 1 ⌊a⌋₊).filter (· ∈ S) ⊆ (Finset.Icc 1 ⌊b⌋₊).filter (· ∈ S) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_le_floor hab)⟩, hp.2⟩
  unfold mertensSum
  rw [← Finset.sum_sdiff hsub]
  ring
end DeletedPrimes
