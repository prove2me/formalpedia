-- Prove2me | solution 1 for BurauFaithful.spec_reduced_fullTwist_sq
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T04:54:52.89179+00:00
-- url     : https://prove2.me/submissions/35607410-7985-4e52-85b3-364668be5d90

/-
`BurauFaithful.spec_reduced_fullTwist_sq`: the specialization at `t = -1` of the 2-dimensional
reduced Burau representation sends the full twist `Δ² = (σ₀σ₁)³` to `-I`.

The matrices `A = !![1,-1;0,1]` and `B = !![2,-1;1,0]` are the images of `σ₀` and `σ₁` (see
`BurauFaithful.spec_reduced_coxeter`, where the same two matrices satisfy the Coxeter relations and
`(A B)^6 = 1`). Here `(A B)^3 = -I`, i.e. the image of the full twist is the central element of
order `2`, so the kernel of the specialization contains `Δ⁴` but not `Δ²`.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem solution :
    ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0]) ^ 3 =
      (-1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  decide
