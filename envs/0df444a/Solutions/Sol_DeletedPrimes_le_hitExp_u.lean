-- Prove2me | solution 1 for DeletedPrimes.le_hitExp_u
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:03:29.268221+00:00
-- url     : https://prove2.me/submissions/25d3e18c-d017-4ecb-8109-853631f19bdc

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
import Theorems.Thm_DeletedPrimes_le_hitExp
import Theorems.Thm_DeletedPrimes_term_u

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α κ u τ c : ℝ} (hκu : κ = k * u)
    (h : ∀ i ≤ k, c ≤ α * i * u + max (κ - τ - i * u) 0) : c ≤ hitExp k α κ τ :=
  le_hitExp fun i hi => by rw [term_u hk hκu]; exact h i hi
end DeletedPrimes
