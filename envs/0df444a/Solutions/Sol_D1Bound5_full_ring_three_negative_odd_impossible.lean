-- Prove2me | solution 1 for D1Bound5.full_ring_three_negative_odd_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:51:12.224185+00:00
-- url     : https://prove2.me/submissions/6edb0366-8319-4756-b316-f892111f248a

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
import Theorems.Thm_D1Bound5_full_ring_positive_integer_square
import Theorems.Thm_D1Bound5_one_three_three_negative_obstruction

section
open scoped NumberField
open Module

namespace D1Bound5
























/-- Three negative odd rational integers cannot form a D(1) triple
in any imaginary quadratic full integer ring. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (x y z : ℤ)
    (hx : x<0) (hy : y<0) (hz : z<0)
    (hxo : x%2=1) (hyo : y%2=1) (hzo : z%2=1)
    (hxy : ∃ r : 𝓞 K, r*r = (x : 𝓞 K)*(y : 𝓞 K)+1)
    (hxz : ∃ r : 𝓞 K, r*r = (x : 𝓞 K)*(z : 𝓞 K)+1)
    (hyz : ∃ r : 𝓞 K, r*r = (y : 𝓞 K)*(z : 𝓞 K)+1) : False := by
  obtain ⟨r,hr⟩ := full_ring_positive_integer_square hK (m := x*y+1)
    (by have := mul_pos_of_neg_of_neg hx hy; omega) (by simpa using hxy)
  obtain ⟨s,hs⟩ := full_ring_positive_integer_square hK (m := x*z+1)
    (by have := mul_pos_of_neg_of_neg hx hz; omega) (by simpa using hxz)
  obtain ⟨t,ht⟩ := full_ring_positive_integer_square hK (m := y*z+1)
    (by have := mul_pos_of_neg_of_neg hy hz; omega) (by simpa using hyz)
  exact one_three_three_negative_obstruction x y z r s t hxo hyo hzo hr hs ht






end D1Bound5
end
