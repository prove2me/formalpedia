-- Prove2me | solution 1 for D1Bound5.full_ring_productFive_growth_of_schur_estimates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:37:54.617547+00:00
-- url     : https://prove2.me/submissions/ea855d9c-ba1a-4948-ad6e-610b9376bdd8

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFiveArithmeticClosure_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_five_schur_det_ne_zero_of_near
import Theorems.Thm_D1Bound5_full_ring_productFive_arithmetic_growth

section
open scoped NumberField BigOperators Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5









/-- The complete arithmetic endpoint of product-five, requiring only the
two analytic estimates for the actual Schur complement. In particular,
nonvanishing of the integral root determinant is proved internally. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (M : Matrix (Fin 5) (Fin 5) (𝓞 K))
    (u : Fin 5 → ℂ)
    (hu : ∀ i, (u i)^2 = phi (a i : K))
    (hdiag : ∀ i, M i i = a i)
    (hsym : ∀ i j, M i j = M j i)
    (hd : fiveLastValue (fun i => phi (a i : K)) ≠ 0)
    (hGnear : ‖fiveNormalizedSchur
        (fun i => phi (a i : K)) u
        (M.map (phi.comp (algebraMap (𝓞 K) K))) - halfOffDiagonal‖ < (1/2 : ℝ))
    (hGsmall : ‖(fiveNormalizedSchur
        (fun i => phi (a i : K)) u
        (M.map (phi.comp (algebraMap (𝓞 K) K)))).det‖ < (1/3 : ℝ)) :
    3 * (∏ i : Fin 4, ‖phi (a (Fin.castAdd 1 i) : K)‖) <
      ‖phi (a 4 : K)‖ := by
  exact full_ring_productFive_arithmetic_growth hK phi a M u
    hu hdiag hsym hd (five_schur_det_ne_zero_of_near _ hGnear) hGsmall

end D1Bound5
end
