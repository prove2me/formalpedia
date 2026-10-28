-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.five_compatible_schur_near
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:38:14.636274+00:00
-- url     : https://prove2.me/submissions/5b92dfc3-11fb-411c-aa34-ae617a2829df

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
import Theorems.Thm_D1Bound5_fiveSignedEntryGood_last_column
import Theorems.Thm_D1Bound5_five_compatible_prefix_operator_bound
import Theorems.Thm_D1Bound5_productFive_prefix_coordinate_div_lt_eighteenth
import Theorems.Thm_D1Bound5_productFive_schur_near_of_coordinate_bounds

section
open scoped NumberField Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5

/-- The Schur complement of a single compatible integral signed root matrix
for an actual ordered D(1) quintuple lies within 1/2 of the reference matrix.
No independent Schur or sign assumptions are made. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (u : Fin 5 → ℂ) (S : Matrix (Fin 5) (Fin 5) (𝓞 K))
    (hu : ∀ i, (u i)^2 = phi (a i : K))
    (hdiag : ∀ i, S i i = a i)
    (hgood : ∀ i j, i ≠ j →
      FiveSignedEntryGood (phi.comp (algebraMap (𝓞 K) K)) a u i j (S i j)) :
    ‖fiveNormalizedSchur (fun i => phi (a i : K)) u
      (S.map (phi.comp (algebraMap (𝓞 K) K))) -
      halfOffDiagonal‖ < (1/2 : ℝ) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let t : Fin 5 → ℂ := fun i => f (a i)
  let E := normalizedRootError t u (fun i j => f (S i j))
  let F := fivePrefixError E
  let v := fiveLastError E
  let w := fivePrefixValues t
  let d := fiveLastValue t
  have hu' : ∀ i, (u i)^2 = f (a i) := hu
  have hg : ∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j) := hgood
  have hF : ‖F-halfOffDiagonal‖ ≤ (11/96 : ℝ) :=
    five_compatible_prefix_operator_bound f a u S hu' hdiag hg
  have hd : (54 : ℝ) ≤ ‖d‖ := by
    have hh := ha.five_last_modulus_gt_fiftyfour hK phi a hmon hB
    exact hh.le
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
  have hlarge :
      2 * ‖t 1‖ * ‖t 2‖ * ‖t 3‖ < ‖t 4‖ := by
    have h := hb.productFour_large_growth hK phi b hbmon hB
    exact h
  have hw : ∀ i, ‖w i / d‖ < (1/18 : ℝ) := by
    intro i
    exact productFive_prefix_coordinate_div_lt_eighteenth t hmon hB hlarge i
  have hcol := fiveSignedEntryGood_last_column f a u S hg
  have hv : ∀ i, ‖v i‖ < (3/4 : ℝ) := by
    intro i
    have hvclose : ‖v i - (1/2 : ℂ)‖ < (1/400 : ℝ) := (hcol i).2
    have hid : v i = (v i - (1/2 : ℂ)) + (1/2 : ℂ) := by ring
    have htri := norm_add_le (v i - (1/2 : ℂ)) (1/2 : ℂ)
    rw [← hid] at htri
    have hhalf : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
    rw [hhalf] at htri
    linarith only [htri, hvclose]
  change ‖productFiveSchur F v w d - halfOffDiagonal‖ < (1/2 : ℝ)
  exact productFive_schur_near_of_coordinate_bounds F v w d hF hd hw hv



end D1Bound5
end
