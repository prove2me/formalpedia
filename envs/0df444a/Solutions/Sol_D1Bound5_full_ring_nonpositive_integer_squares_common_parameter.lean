-- Prove2me | solution 1 for D1Bound5.full_ring_nonpositive_integer_squares_common_parameter
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:56:37.767048+00:00
-- url     : https://prove2.me/submissions/83797012-76d6-45af-a40d-72405edcfb12

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FullRingRationalSquares_Definitions
import Definitions.Def_D1Bound5_OneThreeNegative_Definitions
import Theorems.Thm_D1Bound5_exists_full_integer_coordinates

section
open scoped NumberField
open Module

namespace D1Bound5





/-- A common field parameter works simultaneously for all nonpositive
rational integers which are squares in the full number ring. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) :
    ∃ d : ℤ, 0 < d ∧ ∀ m : ℤ, m ≤ 0 →
      (∃ r : 𝓞 K, r*r = (m : 𝓞 K)) → ∃ y : ℤ, m = -d*y^2 := by
  obtain ⟨d,hd,_,hc⟩ := exists_full_integer_coordinates hK
  refine ⟨d,hd,?_⟩
  intro m hm hs
  rcases hc with ⟨hmod,⟨e⟩⟩ | ⟨_,⟨e⟩⟩
  · obtain ⟨y,hy⟩ := nonpositive_integer_square_trace_one hm
      (integer_square_under_ring_equiv e m hs)
    have he : 4*((d+1)/4)-1=d := by omega
    exact ⟨y, by simpa [he] using hy⟩
  · exact nonpositive_integer_square_trace_zero hm
      (integer_square_under_ring_equiv e m hs)

























end D1Bound5
end
