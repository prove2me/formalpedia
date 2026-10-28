-- Prove2me | solution 1 for D1Bound5.bennettTwoNodes_branch_one_two
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:11.167919+00:00
-- url     : https://prove2.me/submissions/3fe75132-bc1e-479d-844e-8ff90c4470a1

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettTwoNodes_one
import Theorems.Thm_D1Bound5_bennettTwoNodes_two

section
namespace D1Bound5









/-- The two nonzero interpolation columns have exactly the root branches
used in the tuple-root comparison. -/
theorem _root_.solution (a b c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (1 + bennettTwoNodes a b 1 * (a * b * c)⁻¹) ^ (1 / 2 : ℂ) =
        (1 + 1 / (a * c)) ^ (1 / 2 : ℂ) ∧
    (1 + bennettTwoNodes a b 2 * (a * b * c)⁻¹) ^ (1 / 2 : ℂ) =
        (1 + 1 / (b * c)) ^ (1 / 2 : ℂ) := by
  constructor
  · congr 1
    rw [bennettTwoNodes_one]
    field_simp [ha, hb, hc]
    <;> ring
  · congr 1
    rw [bennettTwoNodes_two]
    field_simp [ha, hb, hc]
    <;> ring

end D1Bound5
end
