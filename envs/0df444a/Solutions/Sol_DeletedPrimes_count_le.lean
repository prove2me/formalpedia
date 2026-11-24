-- Prove2me | solution 1 for DeletedPrimes.count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:57:44.144327+00:00
-- url     : https://prove2.me/submissions/2c4225b1-71b6-40f9-9951-14da22235926

import Mathlib
import Definitions.Def_DeletedPrimes_Basic

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) {x : ℝ} (hx : 0 ≤ x) : (count S x : ℝ) ≤ x := by
  unfold count
  have h1 : ((Finset.Icc 1 ⌊x⌋₊).filter (SFree S)).card ≤ ⌊x⌋₊ := by
    calc ((Finset.Icc 1 ⌊x⌋₊).filter (SFree S)).card ≤ (Finset.Icc 1 ⌊x⌋₊).card :=
          Finset.card_filter_le _ _
      _ = ⌊x⌋₊ := by simp
  calc (((Finset.Icc 1 ⌊x⌋₊).filter (SFree S)).card : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ x := Nat.floor_le hx
end DeletedPrimes
