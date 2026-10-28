-- Prove2me | solution 1 for D1Bound5.one_le_norm_integer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:08:11.196448+00:00
-- url     : https://prove2.me/submissions/3267cb86-8a8a-4889-9f59-d06cbd84efb7

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_eq_zero_iff
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
namespace D1Bound5



namespace QuadInt

variable {tau nu : ℤ}











theorem norm_pos (hd : 0 < discriminant tau nu) {z : QuadInt tau nu}
    (hz : z ≠ 0) : 0 < z.norm := by
  have hn := norm_nonneg hd z
  have hne : z.norm ≠ 0 := fun h => hz ((norm_eq_zero_iff hd z).mp h)
  omega

/-- The integer norm of a nonzero element is at least one. -/
theorem one_le_norm (hd : 0 < discriminant tau nu) {z : QuadInt tau nu}
    (hz : z ≠ 0) : 1 ≤ z.norm := by
  have := norm_pos hd hz
  omega



end QuadInt
end D1Bound5
end

section
open scoped NumberField ComplexConjugate
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]







/-- Every nonzero algebraic integer in an imaginary quadratic field has
complex modulus at least one. -/
theorem _root_.solution (hK : finrank ℚ K = 2) (φ : K →+* ℂ)
    {x : 𝓞 K} (hx : x ≠ 0) : 1 ≤ ‖φ (x : K)‖ := by
  obtain ⟨tau, nu, _, hd, ⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  have hz : e.symm x ≠ 0 := by simpa using hx
  have hN : (1 : ℝ) ≤ ((e.symm x).norm : ℝ) := by
    exact_mod_cast QuadInt.one_le_norm hd hz
  have hn : ‖φ (x : K)‖^2 = ((e.symm x).norm : ℝ) := by
    simpa using norm_sq_full_ring_equiv e φ (e.symm x)
  nlinarith [norm_nonneg (φ (x : K))]



end D1Bound5
end
