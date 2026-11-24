-- Prove2me | solution 1 for DeletedPrimes.argmaxExp_u
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:02:07.707948+00:00
-- url     : https://prove2.me/submissions/c7b43d28-3f80-4fa3-b164-7f142fb84850

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (α u : ℝ) :
    argmaxExp k α (k * u) = if α ≤ 1 / 2 then k * u - α * u else (1 - α) * u := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold argmaxExp
  have e1 : α * (k * u) / k = α * u := by rw [div_eq_iff hk0]; ring
  have e2 : k * u * (1 - α) / k = (1 - α) * u := by rw [div_eq_iff hk0]; ring
  rw [e1, e2]
end DeletedPrimes
