-- Prove2me | solution 1 for D1Bound5.full_ring_scaledRootMatrix_det_norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:33:21.335647+00:00
-- url     : https://prove2.me/submissions/ff9b5d00-260f-4508-8f88-bab4c1f2fdf6

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Theorems.Thm_D1Bound5_even_root_matrix_det_ne_zero
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_scaledRootMatrix_det_norm_lower

section
open scoped NumberField BigOperators
open Matrix Module

namespace D1Bound5









/-- The arithmetic lower bound used by the structural determinant estimates. -/
theorem even_root_matrix_one_le_norm {K n : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] [Fintype n] [DecidableEq n]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (hn : Even (Fintype.card n)) (v : n → 𝓞 K) (M : Matrix n n (𝓞 K))
    (hd : ∀ i, M i i = v i)
    (hs : ∀ i j, i ≠ j → (M i j)^2 = v i*v j+1) :
    1 ≤ ‖phi (M.det : K)‖ :=
  one_le_norm_integer hK phi (even_root_matrix_det_ne_zero hK hn v M hd hs)

end D1Bound5
end

section
open scoped NumberField BigOperators
open Module

namespace D1Bound5





/-- For every imaginary quadratic FULL integer ring, the root-square
relations give the arithmetic determinant lower bound in even dimension. -/
theorem _root_.solution
    {K n : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] [Fintype n] [DecidableEq n]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (hn : Even (Fintype.card n))
    (a : n → 𝓞 K) (M : Matrix n n (𝓞 K))
    (hd : ∀ i, M i i = a i)
    (hs : ∀ i j, i ≠ j → (M i j)^2 = a i*a j+1)
    (u : n → ℂ) (hu : ∀ i, (u i)^2 = phi (a i : K)) :
    (∏ i, ‖phi (a i : K)‖) ≤
      ‖(scaledRootMatrix u
        (M.map (phi.comp (algebraMap (𝓞 K) K)))).det‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hdet : 1 ≤ ‖f M.det‖ := even_root_matrix_one_le_norm hK phi hn a M hd hs
  exact scaledRootMatrix_det_norm_lower f a u M hu hdet

end D1Bound5
end
