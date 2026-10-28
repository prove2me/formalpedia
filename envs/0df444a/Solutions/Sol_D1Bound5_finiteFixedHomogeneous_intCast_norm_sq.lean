-- Prove2me | solution 1 for D1Bound5.finiteFixedHomogeneous_intCast_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:28.614908+00:00
-- url     : https://prove2.me/submissions/e1a03336-c19c-4813-b7be-ae6c45a338ff

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
import Theorems.Thm_D1Bound5_finiteFixedHomogeneous_map

section
open scoped NumberField

namespace D1Bound5

/-- Integer-anchor evaluation has the same squared complex modulus as its
quadratic-algebra norm in every coordinate model. No identification of the
ambient number field with the Gaussian field is required. -/
theorem _root_.solution (tau nu : ℤ)
    (n : ℕ) (v : Fin (n+1) → ℤ) (X Y : ℤ) :
    ‖finiteHomogeneousTwo n v (X : ℂ) (Y : ℂ)‖^2 =
      ((finiteHomogeneousTwo n v (X : QuadInt tau nu) (Y : QuadInt tau nu)).norm : ℝ) := by
  let z : ℤ := finiteHomogeneousTwo n v X Y
  have hC : (z : ℂ) = finiteHomogeneousTwo n v (X : ℂ) (Y : ℂ) := by
    simpa [z] using
      finiteFixedHomogeneous_map (Int.castRingHom ℂ) n v X Y
  have hQ : (z : QuadInt tau nu) =
      finiteHomogeneousTwo n v (X : QuadInt tau nu) (Y : QuadInt tau nu) := by
    simpa [z] using
      finiteFixedHomogeneous_map (Int.castRingHom (QuadInt tau nu)) n v X Y
  rw [←hC,←hQ,QuadraticAlgebra.norm_intCast]
  have hn : ‖(z : ℂ)‖ = |(z : ℝ)| := by simp
  rw [hn,sq_abs]
  simp only [Int.cast_pow, Int.cast_id]





end D1Bound5
end
