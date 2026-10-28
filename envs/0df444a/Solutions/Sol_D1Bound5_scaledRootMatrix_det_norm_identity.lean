-- Prove2me | solution 1 for D1Bound5.scaledRootMatrix_det_norm_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:07.595993+00:00
-- url     : https://prove2.me/submissions/437fd348-5c70-4c9c-b651-84a176834d7b

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
import Theorems.Thm_D1Bound5_scaledRootMatrix_det

section
open scoped NumberField BigOperators
open Module

namespace D1Bound5

/-- Exact determinant modulus after scaling a root matrix. This identity
works in an arbitrary source commutative ring and in every finite dimension,
including zero entries and zero auxiliary square roots. -/
theorem _root_.solution
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (f : R →+* ℂ) (a : n → R) (u : n → ℂ)
    (M : Matrix n n R) (hu : ∀ i, (u i)^2 = f (a i)) :
    ‖(scaledRootMatrix u (M.map f)).det‖ =
      (∏ i, ‖f (a i)‖) * ‖f M.det‖ := by
  have hp : (∏ i, u i)^2 = (∏ i, f (a i)) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ => hu i)
  have hmap := RingHom.map_det f M
  change f M.det = (M.map f).det at hmap
  rw [scaledRootMatrix_det, hp, ← hmap, norm_mul, norm_prod]





end D1Bound5
end
