-- Prove2me | solution 1 for D1Bound5.finiteFixedHomogeneous_signed_intCast_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:25.238796+00:00
-- url     : https://prove2.me/submissions/9eddb097-b8bc-4869-a113-de909f07d487

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
import Theorems.Thm_D1Bound5_finiteFixedHomogeneous_intCast_norm_sq
import Theorems.Thm_D1Bound5_finiteFixedHomogeneous_neg

section
open scoped NumberField

namespace D1Bound5



/-- Simultaneous signs preserve the rational coefficient certificate. -/
theorem _root_.solution (tau nu : ℤ)
    (n : ℕ) (v : Fin (n+1) → ℤ) (X Y : ℤ) (sgn : Bool) :
    ‖finiteHomogeneousTwo n v (if sgn then -(X : ℂ) else (X : ℂ))
      (if sgn then -(Y : ℂ) else (Y : ℂ))‖^2 =
      ((finiteHomogeneousTwo n v (X : QuadInt tau nu) (Y : QuadInt tau nu)).norm : ℝ) := by
  cases sgn
  · simpa using
      finiteFixedHomogeneous_intCast_norm_sq tau nu n v X Y
  · simpa [finiteFixedHomogeneous_neg,norm_mul,norm_pow] using
      finiteFixedHomogeneous_intCast_norm_sq tau nu n v X Y



end D1Bound5
end
