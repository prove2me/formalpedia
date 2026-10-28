-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.exists_five_compatible_signed_matrix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:31:54.217854+00:00
-- url     : https://prove2.me/submissions/ae688708-e010-43de-8a0d-6bc12327a929

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
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
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_exists_symmetric_root_matrix
import Theorems.Thm_D1Bound5_IsD1Tuple_five_last_modulus_gt_fiftyfour
import Theorems.Thm_D1Bound5_exists_five_signed_root_matrix_with_bounds

section
namespace D1Bound5

















open scoped NumberField
open Module



/-- The actual ordered full-integer-ring D(1) quintuple supplies every
threshold: no unproved sign-existence or large-last-entry hypothesis remains. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : 1 ≤ ‖phi (a 0 : K)‖) (hB : 3 ≤ ‖phi (a 1 : K)‖) :
    let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
    ∃ (u : Fin 5 → ℂ) (S : Matrix (Fin 5) (Fin 5) (𝓞 K)),
      (∀ i, (u i)^2 = f (a i)) ∧
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i*a j+1) ∧
      (∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j)) ∧
      ‖(fivePrefixError (normalizedRootError (fun i => f (a i)) u
        (fun i j => f (S i j)))).det‖ < (33/128 : ℝ) ∧
      (∀ i : Fin 4,
        ‖fiveLastError (normalizedRootError (fun k => f (a k)) u
          (fun k l => f (S k l))) i - (1/2 : ℂ)‖ < (1/400 : ℝ)) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hone (i : Fin 5) : 1 ≤ ‖f (a i)‖ := hA.trans (hmon (Fin.zero_le i))
  have hthree (i : Fin 5) (hi : i ≠ 0) : 3 ≤ ‖f (a i)‖ := by
    have hle : (1 : Fin 5) ≤ i := by omega
    exact hB.trans (hmon hle)
  have h54 : 54 ≤ ‖f (a 4)‖ :=
    (ha.five_last_modulus_gt_fiftyfour hK phi a hmon hB).le
  have hfirst (i j : Fin 5) (hij : i ≠ j) : 3 ≤ ‖f (a i)*f (a j)‖ := by
    rw [norm_mul]
    by_cases hi : i = 0
    · subst i
      have hi' := hone 0
      have hj' := hthree j hij.symm
      nlinarith [mul_nonneg (sub_nonneg.mpr hi') (sub_nonneg.mpr hj')]
    · have hi' := hthree i hi
      have hj' := hone j
      nlinarith [mul_nonneg (sub_nonneg.mpr hi') (sub_nonneg.mpr hj')]
  have hlater (i j : Fin 5) (_hij : i ≠ j) (h : ¬(i = 0 ∨ j = 0)) :
      9 ≤ ‖f (a i)*f (a j)‖ := by
    rw [norm_mul]
    have hi := hthree i (by tauto)
    have hj := hthree j (by tauto)
    nlinarith [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr hj)]
  have hlast (i j : Fin 5) (_hij : i ≠ j) (h : i = 4 ∨ j = 4) :
      54 ≤ ‖f (a i)*f (a j)‖ := by
    rw [norm_mul]
    rcases h with h | h
    · subst i
      have hj := hone j
      nlinarith [mul_nonneg (sub_nonneg.mpr h54) (sub_nonneg.mpr hj)]
    · subst j
      have hi := hone i
      nlinarith [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr h54)]
  obtain ⟨M, hd, hs, hsq⟩ := ha.exists_symmetric_root_matrix a
  obtain ⟨u, S, hu, hd', hs', _hsgn, hsq', hg, hdet, hcol⟩ :=
    exists_five_signed_root_matrix_with_bounds f a M hd hs hsq hfirst hlater hlast
  exact ⟨u, S, hu, hd', hs', hsq', hg, hdet, hcol⟩




end D1Bound5
end
