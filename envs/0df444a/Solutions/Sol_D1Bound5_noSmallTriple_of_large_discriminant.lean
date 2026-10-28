-- Prove2me | solution 1 for D1Bound5.noSmallTriple_of_large_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:09.533922+00:00
-- url     : https://prove2.me/submissions/b5fa9661-d457-432d-bf9a-cdd7e9180a11

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_QuadInt_discriminant_le_four_bound
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_three_not_square_quadInt

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Among three distinct nonzero integers in [-2,2], two have product 2. -/
theorem three_small_integers_product_two (x y z : ℤ)
    (hxlo : -2 ≤ x) (hxhi : x ≤ 2) (hx0 : x ≠ 0)
    (hylo : -2 ≤ y) (hyhi : y ≤ 2) (hy0 : y ≠ 0)
    (hzlo : -2 ≤ z) (hzhi : z ≤ 2) (hz0 : z ≠ 0)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    x*y = 2 ∨ x*z = 2 ∨ y*z = 2 := by
  interval_cases x <;> interval_cases y <;> interval_cases z <;>
    norm_num at *











end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Above discriminant 32, even three small entries are impossible. -/
theorem _root_.solution {tau nu : ℤ}
    (hlarge : 32 < discriminant tau nu) : ∀ t : Fin 3 → QuadInt tau nu,
      IsD1Tuple t → (∀ i, (t i).norm ≤ 8) → False := by
  intro t ht hnorm
  have hpos : 0 < discriminant tau nu := by omega
  have him (i : Fin 3) : (t i).im = 0 := by
    by_contra h
    have := discriminant_le_four_bound hpos (hnorm i) h
    omega
  have hcast (i : Fin 3) : t i = ((t i).re : QuadInt tau nu) := by
    apply QuadraticAlgebra.ext
    · simp
    · simpa only [QuadraticAlgebra.im_intCast] using him i
  have hb (i : Fin 3) : -2 ≤ (t i).re ∧ (t i).re ≤ 2 ∧ (t i).re ≠ 0 := by
    have hn := hnorm i
    rw [norm_formula, him i] at hn
    simp only [mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at hn
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [sq_nonneg ((t i).re+3)]
    · nlinarith [sq_nonneg ((t i).re-3)]
    · intro h
      apply ht.2.1 i
      rw [hcast i, h]
      simp
  have hne (i j : Fin 3) (hij : i ≠ j) : (t i).re ≠ (t j).re := by
    intro h
    apply hij
    apply ht.1
    rw [hcast i, hcast j, h]
  have hnot (i j : Fin 3) (hij : i ≠ j) (hp : (t i).re*(t j).re = 2) : False := by
    apply three_not_square_quadInt hpos
    obtain ⟨r, hr⟩ := ht.2.2 i j hij
    refine ⟨r, ?_⟩
    rw [hcast i, hcast j, ← Int.cast_mul, hp] at hr
    norm_num at hr
    exact hr
  rcases three_small_integers_product_two (t 0).re (t 1).re (t 2).re
    (hb 0).1 (hb 0).2.1 (hb 0).2.2
    (hb 1).1 (hb 1).2.1 (hb 1).2.2
    (hb 2).1 (hb 2).2.1 (hb 2).2.2
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide)) with h | h | h
  · exact hnot 0 1 (by decide) h
  · exact hnot 0 2 (by decide) h
  · exact hnot 1 2 (by decide) h





end D1Bound5
end
