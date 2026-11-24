-- Prove2me | solution 1 for DeletedPrimes.maxExp_u
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:52:55.926648+00:00
-- url     : https://prove2.me/submissions/b851c792-878d-4bf3-958f-74e81234441a

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (α u : ℝ) :
    maxExp k α (k * u) = if α ≤ 1 / 2 then (α - 1) + 2 * (k * u) - 2 * α * (k * u) + α ^ 2 * u
      else (α - 1) + k * u + (1 - α) ^ 2 * u := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold maxExp
  split_ifs
  · have e : (k : ℝ) * u * (α ^ 2 / k) = α ^ 2 * u := by
      rw [mul_div_assoc', div_eq_iff hk0]; ring
    linear_combination e
  · have e : (k : ℝ) * u * ((1 - α) ^ 2 / k) = (1 - α) ^ 2 * u := by
      rw [mul_div_assoc', div_eq_iff hk0]; ring
    linear_combination e
end DeletedPrimes
