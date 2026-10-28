-- Prove2me | solution 1 for D1Bound5.QuadInt.norm_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:38:50.222647+00:00
-- url     : https://prove2.me/submissions/1c609441-3a3f-421a-b321-e3eae1e8c225

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_four_norm

section
namespace D1Bound5



namespace QuadInt

variable {tau nu : ℤ}









theorem _root_.solution (hd : 0 < discriminant tau nu) (z : QuadInt tau nu) :
    z.norm = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h := four_norm z
    have hy : z.im = 0 := by
      by_contra hy
      have hp := mul_pos hd (sq_pos_of_ne_zero hy)
      nlinarith [sq_nonneg (2*z.re+tau*z.im)]
    have hx : z.re = 0 := by
      rw [hz, hy] at h
      nlinarith
    exact QuadraticAlgebra.ext hx hy
  · intro hz
    simp [hz]







end QuadInt
end D1Bound5
end
