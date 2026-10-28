-- Prove2me | solution 1 for D1Bound5.full_ring_finiteFixedHomogeneous_rational_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:24.646854+00:00
-- url     : https://prove2.me/submissions/9e4dcb31-ed8b-4ca1-9b8f-530c25ee14d7

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
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
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
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Theorems.Thm_D1Bound5_finiteFixedHomogeneous_signed_intCast_norm_sq

section
open scoped NumberField

namespace D1Bound5





/-- Actual full-ring rational anchors transfer the same finite coefficient
certificate in arbitrary number fields, including the row (1,3,8). -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] (phi : K →+* ℂ)
    (tau nu : ℤ) (n : ℕ) (v : Fin (n+1) → ℤ) (X Y : ℤ)
    (sgn : Bool) (x y : 𝓞 K)
    (hx : x = if sgn then -(X : 𝓞 K) else (X : 𝓞 K))
    (hy : y = if sgn then -(Y : 𝓞 K) else (Y : 𝓞 K)) :
    ‖finiteHomogeneousTwo n v (phi (x : K)) (phi (y : K))‖^2 =
      ((finiteHomogeneousTwo n v (X : QuadInt tau nu) (Y : QuadInt tau nu)).norm : ℝ) := by
  have hxC : phi (x : K) = if sgn then -(X : ℂ) else (X : ℂ) := by
    rw [hx]
    cases sgn <;> simp
  have hyC : phi (y : K) = if sgn then -(Y : ℂ) else (Y : ℂ) := by
    rw [hy]
    cases sgn <;> simp
  rw [hxC,hyC]
  exact finiteFixedHomogeneous_signed_intCast_norm_sq tau nu n v X Y sgn

end D1Bound5
end
