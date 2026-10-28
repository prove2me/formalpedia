-- Prove2me | solution 1 for D1Bound5.pairCachedHasSquareRoot_eq_false_of_no_root
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:10.464426+00:00
-- url     : https://prove2.me/submissions/75dbde36-74fa-4bee-939c-64fc1209de13

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff

section
namespace D1Bound5
open QuadInt

/-- An actual nonsquare makes the existing exact cached pair test false,
regardless of the supplied modular signatures. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (x y : PairResidueVertex tau nu)
    (hnot : ¬ ∃ r : QuadInt tau nu, r * r = x.vertex * y.vertex + 1) :
    pairCachedHasSquareRoot sieve x y = false := by
  have hroot : QuadInt.hasSquareRoot (x.vertex * y.vertex + 1) = false := by
    cases hs : QuadInt.hasSquareRoot (x.vertex * y.vertex + 1) with
    | false => rfl
    | true => exact False.elim (hnot ((hasSquareRoot_iff hd _).1 hs))
  simp only [pairCachedHasSquareRoot, hroot, Bool.and_false]















end D1Bound5
end
