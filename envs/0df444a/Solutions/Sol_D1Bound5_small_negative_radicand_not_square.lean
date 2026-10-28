-- Prove2me | solution 1 for D1Bound5.small_negative_radicand_not_square
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:37:46.461608+00:00
-- url     : https://prove2.me/submissions/0d043684-c79a-44fa-9687-a1bf8a8cfc92

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_RationalSquares_Definitions

section
namespace D1Bound5
open QuadInt





/-- The two negative rational radicands are excluded uniformly beyond Δ=32. -/
theorem _root_.solution {tau nu m : ℤ}
    (hlarge : 32 < discriminant tau nu) (hm : m = -1 ∨ m = -3) :
    ¬ ∃ r : QuadInt tau nu, r*r = (m : QuadInt tau nu) := by
  intro hr
  have hm0 : m < 0 := by omega
  obtain ⟨y, hy, _, he⟩ := negative_integer_square_constraint hm0 hr
  have hypos := sq_pos_of_ne_zero hy
  have hyone : 1 ≤ y^2 := by omega
  have hd : 0 ≤ discriminant tau nu := by omega
  have hmul := mul_le_mul_of_nonneg_left hyone hd
  omega





end D1Bound5
end
