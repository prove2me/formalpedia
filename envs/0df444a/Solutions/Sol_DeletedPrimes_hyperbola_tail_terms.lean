-- Prove2me | solution 1 for DeletedPrimes.hyperbola_tail_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:20:03.347557+00:00
-- url     : https://prove2.me/submissions/df03ec18-753e-4643-a37d-19987d3d701d

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {x y β γ : ℝ} (hx : 0 < x) (hy : 0 < y) (hβ : 0 < β) :
    x * ((x / y) ^ β) ^ (1 - 1 / β) = x ^ β * y ^ (1 - β) ∧
    x * ((x / y) ^ β) ^ (-(1 / β)) = y ∧
    x ^ γ * ((x / y) ^ β) ^ (1 - γ / β) = x ^ β * y ^ (γ - β) ∧
    y * (x / y) ^ β = x ^ β * y ^ (1 - β) ∧
    y ^ γ * (x / y) ^ β = x ^ β * y ^ (γ - β) := by
  have hxy : 0 ≤ x / y := (div_pos hx hy).le
  have hβ0 : β ≠ 0 := hβ.ne'
  have hL : ∀ z : ℝ, ((x / y) ^ β) ^ z = x ^ (β * z) * y ^ (-(β * z)) := by
    intro z
    rw [← Real.rpow_mul hxy, Real.div_rpow hx.le hy.le, div_eq_mul_inv, ← Real.rpow_neg hy.le]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hL, show β * (1 - 1 / β) = β - 1 by field_simp, show -(β - 1) = 1 - β by ring,
      Real.rpow_sub_one hx.ne']
    field_simp
  · rw [hL, show β * (-(1 / β)) = -1 by field_simp, neg_neg, Real.rpow_neg_one, Real.rpow_one]
    field_simp
  · rw [hL, show β * (1 - γ / β) = β - γ by field_simp, show -(β - γ) = γ - β by ring,
      ← mul_assoc, ← Real.rpow_add hx]; ring_nf
  · rw [Real.div_rpow hx.le hy.le, div_eq_mul_inv, ← Real.rpow_neg hy.le,
      show (1 : ℝ) - β = -β + 1 by ring, Real.rpow_add hy, Real.rpow_one]
    ring
  · rw [Real.div_rpow hx.le hy.le, div_eq_mul_inv, ← Real.rpow_neg hy.le,
      show γ - β = γ + -β by ring, Real.rpow_add hy]
    ring
end DeletedPrimes
