-- Prove2me | solution 1 for D1Bound5.oneSmallSymmetry_square
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:07:53.805032+00:00
-- url     : https://prove2.me/submissions/f81f5b22-18bf-4756-999d-c427437c5a6d

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
namespace D1Bound5
open QuadInt









theorem _root_.solution {tau nu : ℤ} (sgn conj : Bool)
    (a z : QuadInt tau nu) (h : ∃ r : QuadInt tau nu, r*r = a*z+1) :
    ∃ r : QuadInt tau nu, r*r =
      smallExtensionSymmetry sgn conj a*smallExtensionSymmetry sgn conj z+1 := by
  obtain ⟨r,hr⟩ := h
  have hs : star r*star r = star a*star z+1 := by
    simpa only [star_mul,star_add,star_one,mul_comm] using congrArg star hr
  cases sgn <;> cases conj
  · exact ⟨r,hr⟩
  · exact ⟨star r,hs⟩
  · exact ⟨r,by simpa [smallExtensionSymmetry] using hr⟩
  · exact ⟨star r,by simpa [smallExtensionSymmetry] using hs⟩





end D1Bound5
end
