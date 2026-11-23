-- Prove2me | solution 1 for DeletedPrimes.count_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:17.220226+00:00
-- url     : https://prove2.me/submissions/831af305-fc78-435d-9159-6994b4b060df

import Mathlib
import Definitions.Def_DeletedPrimes_Basic

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : Monotone (count S) := by
  intro x y hxy
  unfold count
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, le_trans hn.1.2 (Nat.floor_le_floor hxy)⟩, hn.2⟩
end DeletedPrimes
