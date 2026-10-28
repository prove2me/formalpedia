-- Prove2me | solution 1 for D1Bound5.bennettTwoResidualGammaBound_mul_rate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:08.771652+00:00
-- url     : https://prove2.me/submissions/2e934ee9-fcb2-44fe-9f10-d619601c148f

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
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoBetaBound_Definitions
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions

section
namespace D1Bound5







/-- Exact normalization of the proved Gamma residual bound by the paper's
exponential rate. No approximation inequality is assumed. -/
theorem _root_.solution
    (A B C δ : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hδ : 0 < δ) (hAC : 1 < A * C) (k : ℕ) :
    bennettTwoResidualGammaBound A B C δ k * (bennettTwoResidualRate A B C δ) ^ k =
      Real.sqrt (1 - 1 / (A * C)) * bennettTwoBetaFactor k := by
  let η : ℝ := 1 - 1 / (A * C)
  let L : ℝ := 4 * δ ^ 2 / (A * B * C ^ 2)
  let R : ℝ := bennettTwoResidualRate A B C δ
  let G : ℝ := Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
    (Real.pi * Real.Gamma (3 * (k : ℝ) + 1))
  have hη : 0 < η := by
    dsimp [η]
    have hdiv := (div_lt_one (mul_pos hA hC)).mpr hAC
    linarith
  have hsqrt : Real.sqrt η ≠ 0 := (Real.sqrt_pos.2 hη).ne'
  have hbase : L * R = (27 / 4 : ℝ) * η ^ 2 := by
    dsimp [L, R, η, bennettTwoResidualRate]
    field_simp [hA.ne', hB.ne', hC.ne', hδ.ne']
    <;> ring
  have hexp : η ^ (2 * (k : ℝ) - 1 / 2) = η ^ (2 * k) / Real.sqrt η := by
    rw [Real.rpow_sub hη, ← Real.sqrt_eq_rpow]
    have hcast : 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Real.rpow_natCast]
  have hratio : η ^ (2 * k) / η ^ (2 * (k : ℝ) - 1 / 2) = Real.sqrt η := by
    rw [hexp]
    field_simp [hη.ne', hsqrt]
  change (L ^ k * G / η ^ (2 * (k : ℝ) - 1 / 2)) * R ^ k =
    Real.sqrt η * bennettTwoBetaFactor k
  calc
    _ = (L * R) ^ k * G / η ^ (2 * (k : ℝ) - 1 / 2) := by rw [mul_pow]; ring
    _ = ((27 / 4 : ℝ) ^ k * G) *
        (η ^ (2 * k) / η ^ (2 * (k : ℝ) - 1 / 2)) := by
      rw [hbase, mul_pow, ← pow_mul]
      ring
    _ = Real.sqrt η * bennettTwoBetaFactor k := by
      rw [hratio]
      unfold bennettTwoBetaFactor
      dsimp [G]
      ring





end D1Bound5
end
