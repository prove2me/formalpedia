-- Prove2me | solution 1 for D1Bound5.first_pair_of_large_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:50:20.819576+00:00
-- url     : https://prove2.me/submissions/a2a22985-00c3-4614-a6c7-6d7fce87c9fe

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
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
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Theorems.Thm_D1Bound5_QuadInt_discriminant_le_four_bound
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_first_pair_root_norm_le_eight

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt

private theorem integer_norm_le_two (x : ℤ) (hpos : 1 ≤ x^2) (hbound : x^2 ≤ 2) :
    x = 1 ∨ x = -1 := by
  have hlo : -1 ≤ x := by nlinarith [sq_nonneg (x+1)]
  have hhi : x ≤ 1 := by nlinarith [sq_nonneg (x-1)]
  interval_cases x <;> norm_num at *

private theorem integer_small_square (x : ℤ) (hx : x^2 ≤ 8)
    (hbig : 9 ≤ (x^2-1)^2) : x^2 = 4 := by
  have hlo : -2 ≤ x := by nlinarith [sq_nonneg (x+2)]
  have hhi : x ≤ 2 := by nlinarith [sq_nonneg (x-2)]
  interval_cases x <;> norm_num at *

/-- The only first pair in any coordinate order of discriminant above 32
is the rational pair (1,3), up to simultaneous sign. -/
theorem _root_.solution {tau nu : ℤ}
    (hlarge : 32 < discriminant tau nu) (a b : QuadInt tau nu)
    (hnorm : FirstPairNorms a b) (hroot : ∃ q, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) := by
  have hd : 0 < discriminant tau nu := by omega
  have hNa : 1 ≤ a.norm ∧ a.norm ≤ 2 := by
    rcases hnorm with h | h <;> omega
  have hNb : 9 ≤ b.norm := by rcases hnorm with h | h <;> omega
  have hprod : a.norm*b.norm ≤ 63 := by
    rcases hnorm with h | h
    · rw [h.1]; simpa using h.2.2
    · rw [h.1]; omega
  obtain ⟨q,hq⟩ := hroot
  have hNq := first_pair_root_norm_le_eight hd a b q hprod hq
  have him (z : QuadInt tau nu) (hz : z.norm ≤ 8) : z.im = 0 := by
    by_contra h
    have := discriminant_le_four_bound hd hz h
    omega
  have hcast (z : QuadInt tau nu) (hz : z.norm ≤ 8) : z = (z.re : QuadInt tau nu) := by
    apply QuadraticAlgebra.ext
    · simp
    · simpa only [QuadraticAlgebra.im_intCast] using him z hz
  have hnormInt (z : QuadInt tau nu) (hz : z.norm ≤ 8) : z.norm = z.re^2 := by
    simp [norm_formula, him z hz]
  have ha8 : a.norm ≤ 8 := by omega
  have hare : a.re = 1 ∨ a.re = -1 := by
    apply integer_norm_le_two
    · simpa only [hnormInt a ha8] using hNa.1
    · simpa only [hnormInt a ha8] using hNa.2
  have ha : a = 1 ∨ a = -1 := by
    rcases hare with h | h
    · left; rw [hcast a ha8, h]; norm_num
    · right; rw [hcast a ha8, h]; norm_num
  have hNa1 : a.norm = 1 := by rcases ha with rfl | rfl <;> norm_num [norm_formula]
  have hNm : (q*q-1).norm = b.norm := by
    have hf : q*q-1 = a*b := by rw [hq]; ring
    rw [hf, map_mul, hNa1, one_mul]
  have hNmi : (q*q-1).norm = (q.re^2-1)^2 := by
    have hc : q*q-1 = ((q.re^2-1 : ℤ) : QuadInt tau nu) := by
      calc
        q*q-1 = (q.re : QuadInt tau nu)*(q.re : QuadInt tau nu)-1 :=
          congrArg (fun z : QuadInt tau nu => z*z-1) (hcast q hNq)
        _ = ((q.re^2-1 : ℤ) : QuadInt tau nu) := by
          push_cast
          ring
    simp only [hc, QuadraticAlgebra.norm_intCast, Int.cast_id]
  have hqfour : q.re^2 = 4 := integer_small_square q.re
    (by simpa only [hnormInt q hNq] using hNq) (by omega)
  have hqfour' : q*q = (4 : QuadInt tau nu) := by
    rw [hcast q hNq, ← Int.cast_mul]
    have h : q.re*q.re = 4 := by nlinarith only [hqfour]
    rw [h]
    norm_num
  rw [hqfour'] at hq
  rcases ha with rfl | rfl
  · exact Or.inl ⟨rfl, by linear_combination -hq⟩
  · exact Or.inr ⟨rfl, by linear_combination hq⟩



end D1Bound5
end
