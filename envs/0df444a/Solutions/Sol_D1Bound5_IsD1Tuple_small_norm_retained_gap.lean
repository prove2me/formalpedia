-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.small_norm_retained_gap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:23:03.425331+00:00
-- url     : https://prove2.me/submissions/dec095ae-26f9-4fd6-a2de-eca0e69a6c8b

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentRetainedMixedForms_Definitions
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_CoherentRetainedRow_parameters
import Theorems.Thm_D1Bound5_FrontierTableRow_parameters
import Theorems.Thm_D1Bound5_IsD1Tuple_productFive_growth
import Theorems.Thm_D1Bound5_IsD1Tuple_small_norm_retained_parameters
import Theorems.Thm_D1Bound5_full_ring_retained_three_mixed_gap
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- Actual one-small-entry retained estimates in every manuscript
small-norm frontier row. The alternatives state the genuine modulus
cutoffs: unit first entries require B≥8 and norm-two first entries
require B≥4; the remaining rows require only B≥3. Both the frontier
and product-five growth inputs are proved from the tuple. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hN8 : ‖phi (a 0 : K)‖^2 ≤ 8)
    (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (hcase :
      (‖phi (a 0 : K)‖^2 = 1 ∧ 8 ≤ ‖phi (a 1 : K)‖) ∨
      (‖phi (a 0 : K)‖^2 = 2 ∧ 4 ≤ ‖phi (a 1 : K)‖) ∨
      ‖phi (a 0 : K)‖^2 = 3 ∨ ‖phi (a 0 : K)‖^2 = 4 ∨
      5 ≤ ‖phi (a 0 : K)‖^2)
    (H lam U : ℝ) (hrow : CoherentRetainedRow H lam U) :
    let v : Fin 3 → ℂ := fun i => phi (a (![0,1,2] i) : K)
    let R := ‖coherentVandermonde3 v‖/(‖phi (a 1 : K)‖*‖phi (a 2 : K)‖^2)
    (9999/10000 : ℝ)/lam^2 *
      (1/R-(51051/400000 : ℝ)/(‖phi (a 0 : K)‖^2*‖phi (a 1 : K)‖^2))^2 *
        (‖phi (a 0 : K)‖^2*‖phi (a 3 : K)‖^5/‖phi (a 2 : K)‖^2) < ‖phi (a 4 : K)‖ ∧
      ‖phi (a 0 : K)‖^2*‖phi (a 3 : K)‖^5/‖phi (a 2 : K)‖^2 < ‖phi (a 4 : K)‖ := by
  classical
  let A := ‖phi (a 0 : K)‖
  let B := ‖phi (a 1 : K)‖
  let S := ‖phi (a 2 : K)‖
  let T := ‖phi (a 3 : K)‖
  have hA : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hAB : A ≤ B := hmon (by decide : (0 : Fin 5) ≤ 1)
  have hBS : B ≤ S := hmon (by decide : (1 : Fin 5) ≤ 2)
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hS0 : 0 < S := hB0.trans_le hBS
  have hpos : 0 < A*B*S := by positivity
  let b : Fin 4 → 𝓞 K := fun i => a (Fin.castAdd 1 i)
  have hcast : Function.Injective (Fin.castAdd 1 : Fin 4 → Fin 5) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin 5 => k.val) hij
  have hb : IsD1Tuple b := by
    refine ⟨ha.1.comp hcast, ?_, ?_⟩
    · intro i
      exact ha.2.1 (Fin.castAdd 1 i)
    · intro i j hij
      exact ha.2.2 (Fin.castAdd 1 i) (Fin.castAdd 1 j) (hcast.ne hij)
  have hbmon : Monotone (fun i => ‖phi (b i : K)‖) := by
    intro i j hij
    exact hmon hij
  have hparameters := IsD1Tuple.small_norm_retained_parameters hK phi b hb hbmon hN8 hB hcase
  have hproduct :
      3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ <
        ‖phi (a 4 : K)‖ := by
    have hc0 : Fin.castAdd 1 (0 : Fin 4) = (0 : Fin 5) := by decide
    have hc1 : Fin.castAdd 1 (1 : Fin 4) = (1 : Fin 5) := by decide
    have hc2 : Fin.castAdd 1 (2 : Fin 4) = (2 : Fin 5) := by decide
    have hc3 : Fin.castAdd 1 (3 : Fin 4) = (3 : Fin 5) := by decide
    simpa only [Fin.prod_univ_four, hc0, hc1, hc2, hc3, mul_assoc] using
      (IsD1Tuple.productFive_growth hK phi a ha hmon hB)
  let Tup : Finset (𝓞 K) := Finset.univ.image a
  have hmem (i : Fin 5) : a i ∈ Tup :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hTup : IsD1 Tup := by
    constructor
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ha.2.1 i
    · intro x hx y hy hxy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      exact ha.2.2 i j (fun hij => hxy (congrArg a hij))
  exact full_ring_retained_three_mixed_gap hK phi hTup a ha.1 hmem
    hA hB hAB hBS hparameters.1 hproduct H lam U hrow
    (hrow.parameters.2.1.trans hparameters.2)

end D1Bound5
end
