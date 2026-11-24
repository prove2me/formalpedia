-- Prove2me | solution 1 for DeletedPrimes.mem_mertens_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:55:15.405743+00:00
-- url     : https://prove2.me/submissions/2380ce0c-2ec2-49c9-9e87-7eaab0a3ae53

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {a b : ℝ} (ha : 0 ≤ a) {p : ℕ}
    (hp : p ∈ (Finset.Icc 1 ⌊b⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊a⌋₊).filter (· ∈ S)) :
    p ∈ S ∧ 1 ≤ p ∧ a < p ∧ (p : ℝ) ≤ b := by
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  have h5 : ⌊a⌋₊ < p := by
    by_contra h
    push Not at h
    exact h4 ⟨⟨h1, h⟩, h3⟩
  exact ⟨h3, h1, (Nat.floor_lt ha).mp h5, (Nat.le_floor_iff' (by omega)).mp h2⟩
end DeletedPrimes
