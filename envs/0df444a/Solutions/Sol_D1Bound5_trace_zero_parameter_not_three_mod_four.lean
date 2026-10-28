-- Prove2me | solution 1 for D1Bound5.trace_zero_parameter_not_three_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:10.256+00:00
-- url     : https://prove2.me/submissions/b00bc313-e6ca-4985-b972-0906779bb104

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_integral_of_quadratic_relation

section
open scoped NumberField
open Module Polynomial

namespace D1Bound5

variable {K : Type*} [Field K]



variable [NumberField K]







/-- If nu is 3 modulo 4 then (1+omega)/2 is an extra integral element.
Thus a trace-zero model with that parameter cannot be the full integer ring. -/
theorem _root_.solution {nu : ℤ}
    (e : QuadInt 0 nu ≃+* 𝓞 K) : nu % 4 ≠ 3 := by
  intro hmod
  let m := (nu+1)/4
  have hm : nu+1 = 4*m := by dsimp [m]; omega
  let f : QuadInt 0 nu →+* K := (algebraMap (𝓞 K) K).comp e.toRingHom
  let w : K := f QuadraticAlgebra.omega
  have hw : w*w = -(nu : K) := by
    have hrel : (QuadraticAlgebra.omega : QuadInt 0 nu)*QuadraticAlgebra.omega = -(nu : QuadInt 0 nu) := by
      ext <;> simp [QuadraticAlgebra.omega]
    simpa only [map_mul, map_neg, map_intCast] using congrArg f hrel
  let r : K := (1+w)/2
  have hmK : (nu : K)+1 = 4*(m : K) := by exact_mod_cast hm
  have hr : r*r = ((-m : ℤ) : K)+(1 : K)*r := by
    dsimp only [r]
    push_cast
    linear_combination (1/4 : K)*hw-(1/4 : K)*hmK
  have hint : IsIntegral ℤ r := integral_of_quadratic_relation (-m) 1 (by simpa only [Int.cast_one] using hr)
  let rO : 𝓞 K := ⟨r, hint⟩
  let y := e.symm rO
  have hy : (2 : QuadInt 0 nu)*y = 1+QuadraticAlgebra.omega := by
    apply e.injective
    simp only [y, map_mul, RingEquiv.apply_symm_apply, map_ofNat, map_add, map_one]
    apply NumberField.RingOfIntegers.ext
    change (2 : K)*r = 1+w
    dsimp only [r]
    ring
  have him : 2*y.im = 1 := by
    have h := congrArg (fun z : QuadInt 0 nu => z.im) hy
    simpa [QuadraticAlgebra.omega, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] using h
  omega

end D1Bound5
end
