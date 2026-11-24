-- Prove2me | solution 1 for DeletedPrimes.le_hitExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:01:02.723933+00:00
-- url     : https://prove2.me/submissions/1f3c4fa5-895d-440d-99bd-ac21e4708beb

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} {α κ τ c : ℝ}
    (h : ∀ i ≤ k, c ≤ α * κ * i / k + max (κ - τ - κ * i / k) 0) : c ≤ hitExp k α κ τ :=
  Finset.le_inf' _ _ fun i hi => h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
end DeletedPrimes
