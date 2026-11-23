-- Prove2me | solution 1 for DeletedPrimes.term_u
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:12.487905+00:00
-- url     : https://prove2.me/submissions/371d697e-6892-4836-9a87-dbad87e7edaf

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α κ u τ : ℝ} (hκu : κ = k * u) (i : ℕ) :
    α * κ * i / k + max (κ - τ - κ * i / k) 0 = α * i * u + max (κ - τ - i * u) 0 := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e1 : α * κ * i / k = α * i * u := by rw [div_eq_iff hk0, hκu]; ring
  have e2 : κ * i / k = i * u := by rw [div_eq_iff hk0, hκu]; ring
  rw [e1, e2]
end DeletedPrimes
