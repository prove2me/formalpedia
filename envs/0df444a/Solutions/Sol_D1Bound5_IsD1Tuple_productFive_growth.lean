-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.productFive_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:17:10.008256+00:00
-- url     : https://prove2.me/submissions/222e1e7f-8784-4802-9cd1-5e717e76e5fe

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_ProductFiveArithmeticClosure_Definitions
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_exists_five_compatible_signed_matrix
import Theorems.Thm_D1Bound5_IsD1Tuple_five_compatible_schur_det_small
import Theorems.Thm_D1Bound5_IsD1Tuple_five_compatible_schur_near
import Theorems.Thm_D1Bound5_IsD1Tuple_five_last_modulus_gt_fiftyfour
import Theorems.Thm_D1Bound5_full_ring_productFive_growth_of_schur_estimates
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5



/-- The product-five growth lemma for an actual ordered D(1) quintuple in the
full ring of integers of every imaginary quadratic field. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB : 3 ≤ ‖phi (a 1 : K)‖) :
    3 * (∏ i : Fin 4, ‖phi (a (Fin.castAdd 1 i) : K)‖) <
      ‖phi (a 4 : K)‖ := by
  have hA : 1 ≤ ‖phi (a 0 : K)‖ :=
    one_le_norm_integer hK phi (ha.2.1 0)
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  obtain ⟨u, S, hu, hdiag, hsym, _hsq, hgood, _hprefix, _hcol⟩ :=
    ha.exists_five_compatible_signed_matrix hK phi a hmon hA hB
  have hnear := ha.five_compatible_schur_near hK phi a hmon hB
    u S hu hdiag hgood
  have hsmall := ha.five_compatible_schur_det_small hK phi a hmon hB
    u S hu hdiag hsym hgood
  have h54 := ha.five_last_modulus_gt_fiftyfour hK phi a hmon hB
  have hd : fiveLastValue (fun i => phi (a i : K)) ≠ 0 := by
    apply norm_pos_iff.mp
    change (0 : ℝ) < ‖phi (a 4 : K)‖
    linarith only [h54]
  exact full_ring_productFive_growth_of_schur_estimates hK phi a S u
    hu hdiag hsym hd hnear hsmall

end D1Bound5
end
