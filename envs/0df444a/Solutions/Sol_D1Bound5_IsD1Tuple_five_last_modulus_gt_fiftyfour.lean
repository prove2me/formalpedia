-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.five_last_modulus_gt_fiftyfour
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:22:13.391333+00:00
-- url     : https://prove2.me/submissions/e033b11c-7df2-43bd-8532-8735aaa2dfdf

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_productFour_large_growth

section
namespace D1Bound5

















open scoped NumberField
open Module

/-- The four large entries give the exact last-entry threshold used in the
last-column sign estimates. This is a consequence of an actual tuple. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB : 3 ≤ ‖phi (a 1 : K)‖) :
    54 < ‖phi (a 4 : K)‖ := by
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
  have hg := hb.productFour_large_growth hK phi b hbmon hB
  change 2 * ‖phi (a 1 : K)‖ * ‖phi (a 2 : K)‖ *
      ‖phi (a 3 : K)‖ < ‖phi (a 4 : K)‖ at hg
  have h2 : 3 ≤ ‖phi (a 2 : K)‖ := hB.trans (hmon (by decide))
  have h3 : 3 ≤ ‖phi (a 3 : K)‖ := hB.trans (hmon (by decide))
  have hp : 9 ≤ ‖phi (a 1 : K)‖ * ‖phi (a 2 : K)‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr h2)]
  have hq := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr h3)
  nlinarith only [hg, hp, h3, hq]






end D1Bound5
end
