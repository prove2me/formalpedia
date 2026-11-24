-- Prove2me | solution 1 for DeletedPrimes.hitExp_le_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:52:44.79383+00:00
-- url     : https://prove2.me/submissions/1575bffa-45ad-4096-a838-60d62447d8be

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} {α κ τ : ℝ} {i : ℕ} (hi : i ≤ k) :
    hitExp k α κ τ ≤ α * κ * i / k + max (κ - τ - κ * i / k) 0 :=
  Finset.inf'_le (fun i : ℕ => α * κ * i / k + max (κ - τ - κ * i / k) 0)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
end DeletedPrimes
