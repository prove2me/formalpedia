-- Prove2me | solution 1 for BoundEntPPT.partialTransposeRect_kronecker_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:01:47.008013+00:00
-- url     : https://prove2.me/submissions/08f7ecc1-b6b3-45fe-b60a-c6bcb464a187

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_BoundEntPPT_partialTransposeRect
open scoped Matrix ComplexOrder

open BoundEntPPT in
theorem solution {I J I₁ J₁ I₂ J₂ : Type*}
    [Fintype I] [Fintype J]
    (A : Matrix I₁ I ℂ) (B : Matrix J₁ J ℂ) (C : Matrix I I₂ ℂ) (D : Matrix J J₂ ℂ)
    (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeRect (Matrix.kronecker A B * X * Matrix.kronecker C D) =
      Matrix.kronecker A Dᵀ * QAlgorithms.Papers.Independent.Information100.P04.gamma X *
        Matrix.kronecker C Bᵀ := by
  ext ⟨i1, j2⟩ ⟨i2, j1⟩
  simp only [partialTransposeRect, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    QAlgorithms.Papers.Independent.Information100.P04.gamma, Finset.sum_mul]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : (I × J) × (I × J) ≃ (I × J) × (I × J) :=
    { toFun := fun z => ((z.1.1, z.2.2), (z.2.1, z.1.2))
      invFun := fun z => ((z.1.1, z.2.2), (z.2.1, z.1.2))
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
  refine Fintype.sum_equiv e _ _ (fun z => ?_)
  simp only [e, Equiv.coe_fn_mk]
  ring
