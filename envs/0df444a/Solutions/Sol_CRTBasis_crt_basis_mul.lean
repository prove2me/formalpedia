-- Prove2me | solution 1 for CRTBasis.crt_basis_mul
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T22:31:32.189119+00:00
-- url     : https://prove2.me/submissions/dd91e55d-fcaa-408d-a573-c1ae1ccd5a95

/-
PR #6453: multiplication in the CRT basis.
-/
import Definitions.Def_Pr6453_CRT

set_option autoImplicit false

namespace CRTBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

/-- In the CRT basis, multiplication by `x` is the diagonal matrix of `x`. -/
theorem toMatrix'_mulLin (x : ι → K) : LinearMap.toMatrix' (mulLin x) = Matrix.diagonal x := by
  ext i j
  rw [LinearMap.toMatrix'_apply, Matrix.diagonal_apply, mulLin_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne (Ne.symm h), h]

/-- Composing multiplications multiplies the matrices: the composite is the diagonal of the product. -/
theorem toMatrix'_mulLin_comp (x y : ι → K) :
    LinearMap.toMatrix' ((mulLin x).comp (mulLin y)) = Matrix.diagonal (x * y) := by
  rw [LinearMap.toMatrix'_comp, toMatrix'_mulLin, toMatrix'_mulLin, Matrix.diagonal_mul_diagonal]
  rfl

/-- **The composite matrix equals multiplication in the CRT basis.** -/
theorem crt_basis_mul (x y : ι → K) :
    LinearMap.toMatrix' ((mulLin x).comp (mulLin y)) = Matrix.diagonal (x * y) ∧
      (LinearMap.toMatrix' (mulLin x)) * (LinearMap.toMatrix' (mulLin y)) =
        Matrix.diagonal (x * y) :=
  ⟨toMatrix'_mulLin_comp x y, by
    rw [toMatrix'_mulLin, toMatrix'_mulLin, Matrix.diagonal_mul_diagonal]; rfl⟩

end CRTBasis

/-- **The composite matrix equals multiplication in the CRT basis.** -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] (x y : ι → K) :
    LinearMap.toMatrix' ((CRTBasis.mulLin x).comp (CRTBasis.mulLin y)) = Matrix.diagonal (x * y) ∧
      (LinearMap.toMatrix' (CRTBasis.mulLin x)) * (LinearMap.toMatrix' (CRTBasis.mulLin y)) =
        Matrix.diagonal (x * y) :=
  CRTBasis.crt_basis_mul x y
