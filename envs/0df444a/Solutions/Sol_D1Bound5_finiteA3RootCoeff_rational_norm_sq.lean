-- Prove2me | solution 1 for D1Bound5.finiteA3RootCoeff_rational_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:20.688267+00:00
-- url     : https://prove2.me/submissions/88cbc056-f3df-486c-92f0-8c9a57861f59

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions
import Theorems.Thm_D1Bound5_full_ring_finiteFixedHomogeneous_rational_norm_sq

section
open scoped NumberField

namespace D1Bound5
open QuadInt



/-- Signed integer anchors have the certified coefficient norms in every
number field. Conjugation fixes the integer anchors automatically. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] (phi : K →+* ℂ)
    (tau nu : ℤ) (X Y : ℤ) (sgn : Bool) (x y : 𝓞 K)
    (hx : x = if sgn then -(X : 𝓞 K) else (X : 𝓞 K))
    (hy : y = if sgn then -(Y : 𝓞 K) else (Y : 𝓞 K))
    (i : Fin 3) (j : Fin 2) (ell : Fin 4) :
    ‖finiteA3RootCoeff (phi (x : K)) (phi (y : K)) i j ell‖^2 =
      ((finiteA3RootCoeff (X : QuadInt tau nu) (Y : QuadInt tau nu) i j ell).norm : ℝ) := by
  fin_cases ell
  all_goals
    simp only [finiteA3RootCoeff, Matrix.cons_val_zero, Matrix.cons_val_succ]
    exact full_ring_finiteFixedHomogeneous_rational_norm_sq phi tau nu _ _ X Y sgn x y hx hy

end D1Bound5
end
