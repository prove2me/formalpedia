-- Prove2me | solution 1 for D1Bound5.scaledRootMatrix_det_norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:50:36.289005+00:00
-- url     : https://prove2.me/submissions/7bce5641-6f2d-4425-b5cd-b82c6af0f68b

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Theorems.Thm_D1Bound5_scaledRootMatrix_det_norm_identity

section
open scoped NumberField BigOperators
open Module

namespace D1Bound5



/-- The determinant bound needs only a lower bound for the unscaled
integral determinant; no nonvanishing hypothesis on the coordinates. -/
theorem _root_.solution
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (f : R →+* ℂ) (a : n → R) (u : n → ℂ)
    (M : Matrix n n R) (hu : ∀ i, (u i)^2 = f (a i))
    (hdet : 1 ≤ ‖f M.det‖) :
    (∏ i, ‖f (a i)‖) ≤ ‖(scaledRootMatrix u (M.map f)).det‖ := by
  rw [scaledRootMatrix_det_norm_identity f a u M hu]
  have hnonneg : 0 ≤ (∏ i, ‖f (a i)‖) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hdet hnonneg]



end D1Bound5
end
