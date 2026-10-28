-- Prove2me | solution 1 for D1Bound5.squarefree_trace_one_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:59:58.746994+00:00
-- url     : https://prove2.me/submissions/5fcf50ed-f7b8-464e-b7bc-268370036166

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_square_division_in_full_ring

section
open scoped NumberField
open Module Polynomial

namespace D1Bound5

variable {K : Type*} [Field K]



variable [NumberField K]





/-- A trace-one coordinate model for a full imaginary quadratic integer
ring has squarefree absolute discriminant. -/
theorem _root_.solution {nu : ℤ}
    (e : QuadInt 1 nu ≃+* 𝓞 K) (hd : 0 < QuadInt.discriminant 1 nu) :
    Squarefree (QuadInt.discriminant 1 nu) := by
  intro a ha
  obtain ⟨m, hm⟩ := ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at hm; omega
  let z : QuadInt 1 nu := 2*QuadraticAlgebra.omega-1
  have hz : z*z = ((a*a*(-m) : ℤ) : QuadInt 1 nu) := by
    have h : 4*nu-1 = a*a*m := by simpa [QuadInt.discriminant] using hm
    apply QuadraticAlgebra.ext
    · simp [z, QuadraticAlgebra.omega, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
      linear_combination -h
    · simp [z, QuadraticAlgebra.omega, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  obtain ⟨y, hy⟩ := square_division_in_full_ring e a (-m) ha0 hz
  have him : a*y.im = 2 := by
    have h := congrArg (fun w : QuadInt 1 nu => w.im) hy
    simpa [z, QuadraticAlgebra.omega, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] using h
  have h : 4*nu-1 = a*a*m := by simpa [QuadInt.discriminant] using hm
  apply isUnit_of_dvd_one
  refine ⟨2*nu*y.im-a*m, ?_⟩
  linear_combination -h-2*nu*him



end D1Bound5
end
