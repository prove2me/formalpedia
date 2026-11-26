-- Prove2me | solution 1 for Erdos287.type_iii_zero_frequency_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T04:44:50.405508+00:00
-- url     : https://prove2.me/submissions/e13db5a2-835c-4785-aa91-25decda9e15a

import Mathlib

set_option autoImplicit false

/-- When a product-constrained sum has one constant coordinate, the complete
sum is independent of the prescribed product. -/
theorem solution (G R : Type) [Group G] [Fintype G] [DecidableEq G] [Semiring R]
    (a : G) (f g : G → R) :
    (∑ z ∈ (Finset.univ : Finset (G × G × G)).filter
        (fun z => (z.1 * z.2.1) * z.2.2 = a), f z.1 * g z.2.1) =
      (∑ x : G, f x) * ∑ y : G, g y := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, ← eq_inv_mul_iff_mul_eq]
  simp [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

