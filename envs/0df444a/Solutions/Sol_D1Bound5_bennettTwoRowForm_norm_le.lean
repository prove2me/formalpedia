-- Prove2me | solution 1 for D1Bound5.bennettTwoRowForm_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:57:47.243644+00:00
-- url     : https://prove2.me/submissions/50c58055-eb97-4dcb-845f-a88b4b0b5ac0

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettIntegralRowSelection_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_bennettTwoNodes_branch_one_two
import Theorems.Thm_D1Bound5_bennettTwoNodes_zero

section
open scoped NumberField
open Module

namespace D1Bound5

/-- Exact comparison of an actual integral row with its analytic residual.
The two signed root products are the same throughout the identity. -/
theorem _root_.solution
    (a b c z sA sB : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hz : z ≠ 0) (k : ℕ) (i : Fin 3) :
    ‖bennettTwoRowForm a b c z sA sB k i‖ ≤
      ‖z‖ * ‖∑ j, bennettTwoClearedEntry a b c k i j *
        (1 + bennettTwoNodes a b j * (a * b * c)⁻¹) ^ (1 / 2 : ℂ)‖ +
      ‖z‖ * (‖bennettTwoClearedEntry a b c k i 1‖ *
          ‖(1 + 1 / (a * c)) ^ (1 / 2 : ℂ) - sA / (a * z)‖ +
        ‖bennettTwoClearedEntry a b c k i 2‖ *
          ‖(1 + 1 / (b * c)) ^ (1 / 2 : ℂ) - sB / (b * z)‖) := by
  let Q : Fin 3 → ℂ := fun j => bennettTwoClearedEntry a b c k i j
  let θA : ℂ := (1 + 1 / (a * c)) ^ (1 / 2 : ℂ)
  let θB : ℂ := (1 + 1 / (b * c)) ^ (1 / 2 : ℂ)
  let R : ℂ := ∑ j, Q j *
    (1 + bennettTwoNodes a b j * (a * b * c)⁻¹) ^ (1 / 2 : ℂ)
  obtain ⟨hA, hB⟩ := bennettTwoNodes_branch_one_two a b c ha hb hc
  have hres : R = Q 0 + Q 1 * θA + Q 2 * θB := by
    dsimp only [R]
    rw [Fin.sum_univ_three, hA, hB]
    simp [bennettTwoNodes_zero, θA, θB]
  have hform : bennettTwoRowForm a b c z sA sB k i =
      z * R + z * (Q 1 * (sA / (a * z) - θA) +
        Q 2 * (sB / (b * z) - θB)) := by
    change Q 0 * z + Q 1 * (sA / a) + Q 2 * (sB / b) = _
    rw [hres]
    field_simp [ha, hb, hz]
    <;> ring
  have hnormA : ‖sA / (a * z) - θA‖ = ‖θA - sA / (a * z)‖ :=
    norm_sub_rev _ _
  have hnormB : ‖sB / (b * z) - θB‖ = ‖θB - sB / (b * z)‖ :=
    norm_sub_rev _ _
  change ‖bennettTwoRowForm a b c z sA sB k i‖ ≤
    ‖z‖ * ‖R‖ + ‖z‖ * (‖Q 1‖ * ‖θA - sA / (a * z)‖ +
      ‖Q 2‖ * ‖θB - sB / (b * z)‖)
  calc
    _ = ‖z * R + z * (Q 1 * (sA / (a * z) - θA) +
        Q 2 * (sB / (b * z) - θB))‖ := congrArg norm hform
    _ ≤ ‖z * R‖ + ‖z * (Q 1 * (sA / (a * z) - θA) +
        Q 2 * (sB / (b * z) - θB))‖ := norm_add_le _ _
    _ = ‖z‖ * ‖R‖ + ‖z‖ * ‖Q 1 * (sA / (a * z) - θA) +
        Q 2 * (sB / (b * z) - θB)‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖z‖ * ‖R‖ + ‖z‖ * (‖Q 1 * (sA / (a * z) - θA)‖ +
        ‖Q 2 * (sB / (b * z) - θB)‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg z))
    _ = _ := by rw [norm_mul, norm_mul, hnormA, hnormB]





end D1Bound5
end
