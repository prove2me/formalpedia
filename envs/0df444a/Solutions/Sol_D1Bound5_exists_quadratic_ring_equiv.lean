-- Prove2me | solution 1 for D1Bound5.exists_quadratic_ring_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:34:04.306386+00:00
-- url     : https://prove2.me/submissions/2a63378f-161e-41f3-8fba-1b0939c2f805

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_exists_integral_generator

section
open scoped NumberField
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K]






/-- Exact ring identification before normalizing the generator's trace. -/
theorem _root_.solution (hK : finrank ℚ K = 2) :
    ∃ tau nu : ℤ, Nonempty (QuadInt tau nu ≃+* 𝓞 K) := by
  obtain ⟨w, hw⟩ := exists_integral_generator hK
  obtain ⟨⟨x,y⟩, hxy⟩ := hw.2 (w*w)
  have hw2 : w*w = x • (1 : 𝓞 K) + y • w := by
    simpa only [zsmul_eq_mul, mul_one] using hxy.symm
  let f : QuadraticAlgebra ℤ x y →ₐ[ℤ] 𝓞 K := QuadraticAlgebra.lift ⟨w, hw2⟩
  have hf : Function.Bijective f := by
    have h := hw.comp (QuadraticAlgebra.equivProd x y).bijective
    change Function.Bijective (fun z : QuadraticAlgebra ℤ x y =>
      (z.re : 𝓞 K)+(z.im : 𝓞 K)*w) at h
    change Function.Bijective (fun z : QuadraticAlgebra ℤ x y => z.re • 1 + z.im • w)
    simpa only [zsmul_eq_mul, mul_one] using h
  refine ⟨y, -x, ?_⟩
  change Nonempty (QuadraticAlgebra ℤ (- -x) y ≃+* 𝓞 K)
  rw [neg_neg]
  exact ⟨(AlgEquiv.ofBijective f hf).toRingEquiv⟩



end D1Bound5
end
