-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.five_compatible_schur_det_small
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:34:17.943623+00:00
-- url     : https://prove2.me/submissions/909fe461-6f6a-443a-bbce-b3d887ee00d0

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
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_five_last_modulus_gt_fiftyfour
import Theorems.Thm_D1Bound5_IsD1Tuple_productFour_large_growth
import Theorems.Thm_D1Bound5_fiveSignedEntryGood_prefix
import Theorems.Thm_D1Bound5_five_compatible_bilinear_p_bound
import Theorems.Thm_D1Bound5_five_compatible_inverse_vector_bound
import Theorems.Thm_D1Bound5_five_compatible_prefix_operator_bound
import Theorems.Thm_D1Bound5_five_normalized_error_symmetric
import Theorems.Thm_D1Bound5_five_prefix_det_upper_of_mixed_signed_entries
import Theorems.Thm_D1Bound5_five_prefix_symmetric
import Theorems.Thm_D1Bound5_five_schur_det_ne_zero_of_near
import Theorems.Thm_D1Bound5_productFive_cross_div_norm_lt_11_108
import Theorems.Thm_D1Bound5_productFive_p_div_sq_norm_lt
import Theorems.Thm_D1Bound5_productFive_prefix_l2_lt_last_div_nine
import Theorems.Thm_D1Bound5_productFive_quadratic_q_div_norm_lt
import Theorems.Thm_D1Bound5_productFive_schur_det_upper_of_bilinear_bounds

section
open scoped NumberField Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5

/-- One compatible signed integral root matrix attached to an actual ordered
D(1) quintuple satisfies the sharp Schur determinant estimate. The size,
sign, inverse and bilinear hypotheses are derived from the tuple itself. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (u : Fin 5 → ℂ) (S : Matrix (Fin 5) (Fin 5) (𝓞 K))
    (hu : ∀ i, (u i)^2 = phi (a i : K))
    (hdiag : ∀ i, S i i = a i)
    (hSsym : ∀ i j, S i j = S j i)
    (hgood : ∀ i j, i ≠ j →
      FiveSignedEntryGood (phi.comp (algebraMap (𝓞 K) K)) a u i j (S i j)) :
    ‖(fiveNormalizedSchur (fun i => phi (a i : K)) u
      (S.map (phi.comp (algebraMap (𝓞 K) K)))).det‖ < (1/3 : ℝ) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let t : Fin 5 → ℂ := fun i => f (a i)
  let E := normalizedRootError t u (fun i j => f (S i j))
  let F := fivePrefixError E
  let v := fiveLastError E
  let w := fivePrefixValues t
  let d := fiveLastValue t
  have hu' : ∀ i, (u i)^2 = f (a i) := hu
  have hg : ∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j) := hgood
  have hF : ‖F - halfOffDiagonal‖ ≤ (11/96 : ℝ) :=
    five_compatible_prefix_operator_bound f a u S hu' hdiag hg
  have hFsmall : ‖F - halfOffDiagonal‖ < (1/8 : ℝ) :=
    lt_of_le_of_lt hF (by norm_num)
  have hFhalf : ‖F - halfOffDiagonal‖ < (1/2 : ℝ) :=
    lt_trans hFsmall (by norm_num)
  have hFdet : F.det ≠ 0 := five_schur_det_ne_zero_of_near F hFhalf
  have hMsym : (S.map f)ᵀ = S.map f := by
    ext i j
    change f (S j i) = f (S i j)
    rw [hSsym]
  have hFsym : Fᵀ = F :=
    five_prefix_symmetric E (five_normalized_error_symmetric t u (S.map f) hMsym)
  have h54 : (54 : ℝ) ≤ ‖d‖ := by
    have hh := ha.five_last_modulus_gt_fiftyfour hK phi a hmon hB
    exact hh.le
  have hd : d ≠ 0 := norm_pos_iff.mp (by linarith only [h54])
  let b : Fin 4 → 𝓞 K := fun i => a i.succ
  have hb : IsD1Tuple b := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j h
      apply Fin.ext
      have h' := congrArg (fun k : Fin 5 => k.val) (ha.1 h)
      simpa using h'
    · intro i
      exact ha.2.1 i.succ
    · intro i j hij
      exact ha.2.2 i.succ j.succ (by
        intro h
        apply hij
        apply Fin.ext
        have h' := congrArg (fun k : Fin 5 => k.val) h
        simpa using h')
  have hbmon : Monotone (fun i => ‖phi (b i : K)‖) := by
    intro i j hij
    apply hmon
    change i.val+1 ≤ j.val+1
    change i.val ≤ j.val at hij
    omega
  have hlarge : 2 * ‖t 1‖ * ‖t 2‖ * ‖t 3‖ < ‖t 4‖ := by
    have hh := hb.productFour_large_growth hK phi b hbmon hB
    exact hh
  have hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ < ‖d‖/9 :=
    productFive_prefix_l2_lt_last_div_nine t hmon hB hlarge
  have hIv : ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v) :
      EuclideanSpace ℂ (Fin 4))‖ < (11/12 : ℝ) :=
    five_compatible_inverse_vector_bound f a u S hu' hdiag hg
  have hp : ‖v ⬝ᵥ (F⁻¹ *ᵥ v)‖ < (1 : ℝ) :=
    five_compatible_bilinear_p_bound f a u S hu' hdiag hg
  have hh : ‖(v ⬝ᵥ (F⁻¹ *ᵥ w))/d‖ < (11/108 : ℝ) :=
    productFive_cross_div_norm_lt_11_108 F v w d hd hFsym hw hIv
  have hq : ‖(w ⬝ᵥ (F⁻¹ *ᵥ w))/d^2‖ < (8/243 : ℝ) :=
    productFive_quadratic_q_div_norm_lt F w d hd hFsmall hw
  have hpd : ‖(v ⬝ᵥ (F⁻¹ *ᵥ v))/d^2‖ < (1/2916 : ℝ) :=
    productFive_p_div_sq_norm_lt _ d hp h54
  have hprefix : ‖F.det‖ < (33/128 : ℝ) :=
    five_prefix_det_upper_of_mixed_signed_entries f a u S
      hu' hdiag hSsym (fiveSignedEntryGood_prefix f a u S hg)
  change ‖(productFiveSchur F v w d).det‖ < (1/3 : ℝ)
  exact productFive_schur_det_upper_of_bilinear_bounds
    F v w d hFdet hd hFsym hprefix.le hh.le hp.le hq.le hpd.le



end D1Bound5
end
