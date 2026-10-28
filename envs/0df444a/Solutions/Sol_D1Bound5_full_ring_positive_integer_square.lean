-- Prove2me | solution 1 for D1Bound5.full_ring_positive_integer_square
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:54:18.358996+00:00
-- url     : https://prove2.me/submissions/19d32ab7-0842-49e8-b7a4-ce63bdc9a09a

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FullRingRationalSquares_Definitions
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_positive_integer_square_is_integer

section
open scoped NumberField
open Module

namespace D1Bound5



/-- A positive rational integer square in the full number ring is an
ordinary integer square, uniformly over all imaginary quadratic fields. -/
theorem _root_.solution {K : Type*} [Field K]
    [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {m : ℤ} (hm : 0 < m)
    (hs : ∃ r : 𝓞 K, r*r = (m : 𝓞 K)) :
    ∃ n : ℤ, m = n^2 := by
  obtain ⟨tau,nu,_,hd,⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  exact positive_integer_square_is_integer hd hm (integer_square_under_ring_equiv e m hs)



end D1Bound5
end
