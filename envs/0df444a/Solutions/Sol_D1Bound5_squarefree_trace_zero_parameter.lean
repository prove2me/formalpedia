-- Prove2me | solution 1 for D1Bound5.squarefree_trace_zero_parameter
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:54:19.152141+00:00
-- url     : https://prove2.me/submissions/dbb4f174-a8a9-4ab8-9524-29cf512b3291

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



/-- A trace-zero coordinate model for a full imaginary quadratic integer
ring has squarefree nu. -/
theorem _root_.solution {nu : ℤ}
    (e : QuadInt 0 nu ≃+* 𝓞 K) (hd : 0 < QuadInt.discriminant 0 nu) : Squarefree nu := by
  have hnu : 0 < nu := by unfold QuadInt.discriminant at hd; norm_num at hd; omega
  intro a ha
  obtain ⟨m, hm⟩ := ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at hm; omega
  have hz : (QuadraticAlgebra.omega : QuadInt 0 nu)*QuadraticAlgebra.omega =
      ((a*a*(-m) : ℤ) : QuadInt 0 nu) := by
    ext <;> simp [QuadraticAlgebra.omega, hm]
  obtain ⟨y, hy⟩ := square_division_in_full_ring e a (-m) ha0 hz
  have him : a*y.im = 1 := by
    have h := congrArg (fun z : QuadInt 0 nu => z.im) hy
    simpa [QuadraticAlgebra.omega] using h
  exact isUnit_of_dvd_one ⟨y.im, him.symm⟩





end D1Bound5
end
