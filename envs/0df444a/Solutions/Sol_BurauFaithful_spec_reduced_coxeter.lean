-- Prove2me | solution 1 for BurauFaithful.spec_reduced_coxeter
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-29T17:30:29.71409+00:00
-- url     : https://prove2.me/submissions/5115395c-46d9-4fb7-a028-3f7bcfba5a90

/-
`BurauFaithful.spec_reduced_coxeter`: the two integral matrices that are the images of `σ₀` and `σ₁`
under the specialization at `t = -1` of the 2-dimensional reduced Burau representation satisfy the
defining relations of the Coxeter-Moser presentation of the homogeneous modular group
`M₂ = SL(2,ℤ)`:

  `A B A = B A B`,  `(A B A)^4 = 1`,  `det A = det B = 1`,

together with `(A B)^6 = 1` (the image of `Δ⁴ = (σ₀σ₁)^6`, the kernel generator).
All five statements are finite computations over `ℤ`.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

theorem solution :
    ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0] * !![1, -1; 0, 1] =
        !![2, -1; 1, 0] * !![1, -1; 0, 1] * !![2, -1; 1, 0]) ∧
      ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0] * !![1, -1; 0, 1]) ^ 4 =
        1 ∧
      (!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∧
      (!![2, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∧
      ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0]) ^ 6 = 1 := by
  decide
