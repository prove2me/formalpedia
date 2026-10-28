-- Prove2me | solution 1 for D1Bound5.discrete_two_square_sub_one_norm_sq_ge_seven
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:19.647981+00:00
-- url     : https://prove2.me/submissions/5d7a6655-322f-415c-925f-97e67025322c

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_D1Bound5_complex_two_square_sub_one_norm_sq_ge_seven

section
open scoped NumberField
open Module

namespace D1Bound5



/-- In a discrete complex image, a nonzero square root whose square is
not one automatically supplies the three distance bounds. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (hdiscrete : ∀ x : R, x ≠ 0 → 1 ≤ ‖f x‖)
    (r : R) (hr : r ≠ 0) (hrsq : r ^ 2 ≠ 1) :
    7 ≤ ‖(2 : ℂ) * (f r) ^ 2 - 1‖ ^ 2 := by
  have hp : r + 1 ≠ 0 := by
    intro h
    have he : r = -1 := by linear_combination h
    apply hrsq
    rw [he]
    ring
  have hm : r - 1 ≠ 0 := by
    intro h
    have he : r = 1 := sub_eq_zero.mp h
    apply hrsq
    rw [he]
    ring
  exact complex_two_square_sub_one_norm_sq_ge_seven (f r) (hdiscrete r hr)
    (by simpa only [map_add, map_one] using hdiscrete (r + 1) hp)
    (by simpa only [map_sub, map_one] using hdiscrete (r - 1) hm)



end D1Bound5
end
