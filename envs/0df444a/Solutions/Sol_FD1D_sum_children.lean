-- Prove2me | solution 1 for FD1D.sum_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:48:47.189802+00:00
-- url     : https://prove2.me/submissions/7c174a26-5b9d-449e-b021-a93bf3fd8dfe

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution {M : Type*} [AddCommMonoid M] (d : ℕ)
    (f : DyadicNode (d + 1) → M) :
    ∑ w, f w = ∑ v, (f (leftChild v) + f (rightChild v)) := by
  calc
    ∑ w, f w = ∑ x : DyadicNode d × Fin 2, f (childrenEquiv d x) := by
      symm
      exact (childrenEquiv d).sum_comp f
    _ = ∑ v, ∑ side : Fin 2, f (childrenEquiv d (v, side)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ v, (f (leftChild v) + f (rightChild v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Fin.sum_univ_two]
      rfl
end FD1D
