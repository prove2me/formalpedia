-- Prove2me | solution 1 for D1Bound5.square_division_in_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:12.103564+00:00
-- url     : https://prove2.me/submissions/b54c340b-46c1-4fb7-b649-73dcae44c7d6

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
open scoped NumberField
open Module Polynomial

namespace D1Bound5

variable {K : Type*} [Field K]



variable [NumberField K]

/-- Square divisibility in a full integer ring forces divisibility of the
root. This uses integrality in K, not unique factorization in the ring. -/
theorem _root_.solution {tau nu : ℤ}
    (e : QuadInt tau nu ≃+* 𝓞 K) (a m : ℤ) (ha : a ≠ 0)
    {z : QuadInt tau nu} (hz : z*z = ((a*a*m : ℤ) : QuadInt tau nu)) :
    ∃ y : QuadInt tau nu, (a : QuadInt tau nu)*y = z := by
  let f : QuadInt tau nu →+* K := (algebraMap (𝓞 K) K).comp e.toRingHom
  let r : K := f z / (a : K)
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  have hr : r^2 = (m : K) := by
    dsimp only [r]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 haK)).mpr
    have h := congrArg f hz
    simp only [map_mul, map_intCast] at h
    push_cast at h
    linear_combination h
  have hint : IsIntegral ℤ r := IsIntegral.of_pow (by decide : 0 < 2) (by
    rw [hr]
    exact isIntegral_intCast m)
  let y : 𝓞 K := ⟨r, hint⟩
  refine ⟨e.symm y, ?_⟩
  apply e.injective
  rw [map_mul, RingEquiv.apply_symm_apply, map_intCast]
  apply NumberField.RingOfIntegers.ext
  change (a : K)*r = f z
  dsimp only [r]
  field_simp [haK]







end D1Bound5
end
