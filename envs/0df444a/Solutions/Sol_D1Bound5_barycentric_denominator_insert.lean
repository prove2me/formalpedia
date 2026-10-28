-- Prove2me | solution 1 for D1Bound5.barycentric_denominator_insert
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:25.908307+00:00
-- url     : https://prove2.me/submissions/d9bfa09f-0c87-4085-877f-202c5bf01615

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5

/-- An old barycentric denominator acquires the new-node difference. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (t i : ι)
    (ht : t ∉ s) (hi : i ∈ s) :
    (∏ j ∈ (insert t s).erase i, (a i - a j)) =
      (a i - a t) * ∏ j ∈ s.erase i, (a i - a j) := by
  have hne : t ≠ i := by
    intro heq
    exact ht (by simpa [heq] using hi)
  rw [Finset.erase_insert_of_ne hne]
  rw [Finset.prod_insert (by simp [ht])]





end D1Bound5
end
