-- Prove2me | solution 1 for D1Bound5.small_pair_of_large_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:46:03.918903+00:00
-- url     : https://prove2.me/submissions/5bafe766-5dc1-4fbf-98b1-b847d54fc36b

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
import Theorems.Thm_D1Bound5_QuadInt_discriminant_le_four_bound
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_small_negative_radicand_not_square
import Theorems.Thm_D1Bound5_three_not_square_quadInt

section
namespace D1Bound5
open QuadInt

/-- Only four radicands can arise from distinct nonzero rational small entries. -/
theorem small_integer_pair_radicands (x y : ℤ)
    (hxlo : -2 ≤ x) (hxhi : x ≤ 2) (hx0 : x ≠ 0)
    (hylo : -2 ≤ y) (hyhi : y ≤ 2) (hy0 : y ≠ 0) (hxy : x ≠ y) :
    x*y+1 = 3 ∨ x*y+1 = -1 ∨ x*y+1 = -3 ∨ x*y+1 = 0 := by
  interval_cases x <;> interval_cases y <;> norm_num at *

/-- A zero radicand in the rational small disk is exactly the unit pair. -/
theorem small_integer_pair_zero (x y : ℤ)
    (hxlo : -2 ≤ x) (hxhi : x ≤ 2)
    (hylo : -2 ≤ y) (hyhi : y ≤ 2) (hxy : x*y+1 = 0) :
    (x = -1 ∧ y = 1) ∨ (x = 1 ∧ y = -1) := by
  interval_cases x <;> interval_cases y <;> norm_num at *



/-- For discriminant above 32, the only compatible small pair is {-1,1}.
This includes zero roots and makes no maximal-order or squarefree assumption. -/
theorem _root_.solution {tau nu : ℤ}
    (hlarge : 32 < discriminant tau nu) (a b : QuadInt tau nu)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8)
    (hsquare : ∃ r, r*r = a*b+1) :
    (a = -1 ∧ b = 1) ∨ (a = 1 ∧ b = -1) := by
  have hd : 0 < discriminant tau nu := by omega
  have him (z : QuadInt tau nu) (hz : z.norm ≤ 8) : z.im = 0 := by
    by_contra h
    have := discriminant_le_four_bound hd hz h
    omega
  have hcast (z : QuadInt tau nu) (hz : z.norm ≤ 8) : z = (z.re : QuadInt tau nu) := by
    apply QuadraticAlgebra.ext
    · simp
    · simpa only [QuadraticAlgebra.im_intCast] using him z hz
  have hbnd (z : QuadInt tau nu) (hz : z.norm ≤ 8) (hz0 : z ≠ 0) :
      -2 ≤ z.re ∧ z.re ≤ 2 ∧ z.re ≠ 0 := by
    have hn := hz
    rw [norm_formula, him z hz] at hn
    simp only [mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at hn
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [sq_nonneg (z.re+3)]
    · nlinarith [sq_nonneg (z.re-3)]
    · intro h
      apply hz0
      rw [hcast z hz, h]
      simp
  have hneq : a.re ≠ b.re := by
    intro h
    apply hab
    rw [hcast a hNa, hcast b hNb, h]
  have hba := hbnd a hNa ha
  have hbb := hbnd b hNb hb
  have hrational : ∃ r : QuadInt tau nu,
      r*r = ((a.re*b.re+1 : ℤ) : QuadInt tau nu) := by
    obtain ⟨r, hr⟩ := hsquare
    refine ⟨r, ?_⟩
    rw [hcast a hNa, hcast b hNb] at hr
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using hr
  have hzero : a.re*b.re+1 = 0 := by
    rcases small_integer_pair_radicands a.re b.re
      hba.1 hba.2.1 hba.2.2 hbb.1 hbb.2.1 hbb.2.2 hneq with h | h | h | h
    · apply False.elim
      apply three_not_square_quadInt hd
      simpa [h] using hrational
    · exact False.elim (small_negative_radicand_not_square hlarge (Or.inl h) hrational)
    · exact False.elim (small_negative_radicand_not_square hlarge (Or.inr h) hrational)
    · exact h
  rcases small_integer_pair_zero a.re b.re hba.1 hba.2.1 hbb.1 hbb.2.1 hzero with h | h
  · left
    constructor
    · rw [hcast a hNa, h.1]
      norm_num
    · rw [hcast b hNb, h.2]
      norm_num
  · right
    constructor
    · rw [hcast a hNa, h.1]
      norm_num
    · rw [hcast b hNb, h.2]
      norm_num



end D1Bound5
end
