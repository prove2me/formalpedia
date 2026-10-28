-- Prove2me | solution 1 for D1Bound5.even_root_matrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:46:27.379558+00:00
-- url     : https://prove2.me/submissions/76d17b85-5d4c-4ae7-b89b-878d0e005bb2

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_EvenDeterminant_Definitions
import Theorems.Thm_D1Bound5_even_root_matrix_det_sq_char_two
import Theorems.Thm_D1Bound5_exists_normalized_quadratic_ring_equiv

section
open scoped NumberField BigOperators
open Matrix Module

namespace D1Bound5







/-- The even-dimensional integral root matrix is nonsingular over the
full integer ring of every quadratic number field. No quotient properness
assumption is added: the explicit reduction has a nontrivial target. -/
theorem _root_.solution {K n : Type*} [Field K] [NumberField K]
    [Fintype n] [DecidableEq n] (hK : finrank ℚ K = 2)
    (hn : Even (Fintype.card n)) (v : n → 𝓞 K) (M : Matrix n n (𝓞 K))
    (hd : ∀ i, M i i = v i)
    (hs : ∀ i j, i ≠ j → (M i j)^2 = v i*v j+1) : M.det ≠ 0 := by
  obtain ⟨tau,nu,_,⟨e⟩⟩ := exists_normalized_quadratic_ring_equiv hK
  let S := QuadraticAlgebra (ZMod 2) (-(nu : ZMod 2)) (tau : ZMod 2)
  letI : CharP S 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
    apply QuadraticAlgebra.ext
    · change (2 : ZMod 2) = 0
      exact CharTwo.two_eq_zero
    · rfl)
  let f : 𝓞 K →+* S := (quadraticReductionTwo tau nu).comp e.symm.toRingHom
  have hdiag (i : n) : (M.map f) i i = f (v i) := by simp [hd]
  have hsquare (i j : n) (hij : i ≠ j) :
      ((M.map f) i j)^2 = f (v i)*f (v j)+1 := by
    simpa only [Matrix.map_apply,map_pow,map_mul,map_add,map_one]
      using congrArg f (hs i j hij)
  have h := even_root_matrix_det_sq_char_two hn (fun i => f (v i)) (M.map f) hdiag hsquare
  change (f.mapMatrix M).det^2 = 1 at h
  rw [← RingHom.map_det f M] at h
  intro hzero
  rw [hzero,map_zero,zero_pow (by decide : 2 ≠ 0)] at h
  exact zero_ne_one h



end D1Bound5
end
