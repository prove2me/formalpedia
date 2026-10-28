-- Prove2me | solution 1 for D1Bound5.crossBlock_scaled_det_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:18.09072+00:00
-- url     : https://prove2.me/submissions/79b84547-62e8-4795-8a13-bd9b3b4f1267

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5



/-- Squared modulus of the cross-block determinant after the two scaling
steps. Stating the identity with squares avoids real square-root choices. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a b : Fin 3 → R) (u v : Fin 3 → ℂ)
    (S : Fin 3 → Fin 3 → R)
    (hu : ∀ i, (u i)^2 = f (a i)) (hv : ∀ j, (v j)^2 = f (b j)) :
    ‖Matrix.det (Matrix.of (fun i j => (f (a i)*u i)*f (S i j)*(f (b j)*v j)))‖^2 =
      ((‖f (a 0)‖*‖f (b 0)‖)*(‖f (a 1)‖*‖f (b 1)‖)*
        (‖f (a 2)‖*‖f (b 2)‖))^3*‖f (Matrix.det (Matrix.of S))‖^2 := by
  let T : Fin 3 → Fin 3 → ℂ :=
    fun i j => (f (a i)*u i)*f (S i j)*(f (b j)*v j)
  have hT : Matrix.of T = Matrix.diagonal (fun i => f (a i)*u i) * (Matrix.map (Matrix.of S) f) *
      Matrix.diagonal (fun j => f (b j)*v j) := by
    ext i j
    simp only [T, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.of_apply]
  have hmap := RingHom.map_det f (Matrix.of S)
  change f (Matrix.det (Matrix.of S)) = Matrix.det (Matrix.map (Matrix.of S) f) at hmap
  have hdet : (Matrix.det (Matrix.of T)) = (∏ i, f (a i)*u i)*f (Matrix.det (Matrix.of S))*(∏ j, f (b j)*v j) := by
    rw [hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, ← hmap]
  have hleft : (∏ i, f (a i)*u i)^2 = (∏ i, f (a i))^3 := by
    rw [← Finset.prod_pow, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_pow, hu i]
    ring
  have hright : (∏ j, f (b j)*v j)^2 = (∏ j, f (b j))^3 := by
    rw [← Finset.prod_pow, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro j _
    rw [mul_pow, hv j]
    ring
  have hsquare : (Matrix.det (Matrix.of T))^2 = ((∏ i, f (a i))*(∏ j, f (b j)))^3*(f (Matrix.det (Matrix.of S)))^2 := by
    rw [hdet]
    calc
      _ = (∏ i, f (a i)*u i)^2*(∏ j, f (b j)*v j)^2*(f (Matrix.det (Matrix.of S)))^2 := by ring
      _ = ((∏ i, f (a i))*(∏ j, f (b j)))^3*(f (Matrix.det (Matrix.of S)))^2 := by
        rw [hleft, hright]
        ring
  have hnorm := congrArg norm hsquare
  simp only [norm_pow, norm_mul, norm_prod] at hnorm
  change ‖(Matrix.det (Matrix.of T))‖^2 = _
  rw [hnorm, Fin.prod_univ_three, Fin.prod_univ_three]
  ring







end D1Bound5
end
