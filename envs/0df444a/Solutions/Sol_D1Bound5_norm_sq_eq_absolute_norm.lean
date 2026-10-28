-- Prove2me | solution 1 for D1Bound5.norm_sq_eq_absolute_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:19:45.853895+00:00
-- url     : https://prove2.me/submissions/9d89c3d1-18b6-4a7b-99fb-b0d79e3d2846

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
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
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The coordinate polynomial norm is exactly mathlib's algebraic norm. -/
theorem QuadInt.algebra_norm_eq {tau nu : ℤ} (z : QuadInt tau nu) :
    Algebra.norm ℤ z = z.norm := by
  rw [Algebra.norm_apply]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

/-- Full-ring equivalences preserve the integral algebraic norm. -/
theorem algebra_norm_ring_equiv {K : Type*} [Field K] {tau nu : ℤ}
    (e : QuadInt tau nu ≃+* 𝓞 K) (z : QuadInt tau nu) :
    Algebra.norm ℤ (e z) = z.norm := by
  let eA : QuadInt tau nu ≃ₐ[ℤ] 𝓞 K := { e with commutes' := by intro n; simp }
  exact (Algebra.norm_eq_of_algEquiv eA z).trans (QuadInt.algebra_norm_eq z)

/-- The absolute algebraic norm is the squared modulus at every complex
embedding of an imaginary quadratic field. -/
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (hK : finrank ℚ K = 2) (φ : K →+* ℂ) (x : 𝓞 K) :
    ‖φ (x : K)‖^2 = (Algebra.norm ℤ x : ℝ) := by
  obtain ⟨tau, nu, _, _, ⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  have hn := algebra_norm_ring_equiv e (e.symm x)
  rw [RingEquiv.apply_symm_apply] at hn
  rw [hn]
  simpa using norm_sq_full_ring_equiv e φ (e.symm x)

end D1Bound5
end
