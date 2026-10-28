-- Prove2me | solution 1 for D1Bound5.finiteQ_half_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:41.648478+00:00
-- url     : https://prove2.me/submissions/d991f87f-e5bc-49ef-856a-16e04766a670

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence

section
open Finset

namespace D1Bound5

theorem _root_.solution :
    halfBinomialCoeff 0 = 1 ∧ halfBinomialCoeff 1 = 1/2 ∧
    halfBinomialCoeff 2 = -1/8 ∧ halfBinomialCoeff 3 = 1/16 ∧
    halfBinomialCoeff 4 = -5/128 := by
  have h0 : halfBinomialCoeff 0 = 1 := by simp [halfBinomialCoeff]
  have h1 : halfBinomialCoeff 1 = 1/2 := by
    norm_num [halfBinomialCoeff, Ring.choose_one_right]
  have h2 : halfBinomialCoeff 2 = -1/8 := by
    have h := halfBinomialCoeff_recurrence 1
    norm_num [h1] at h
    linarith
  have h3 : halfBinomialCoeff 3 = 1/16 := by
    have h := halfBinomialCoeff_recurrence 2
    norm_num [h2] at h
    linarith
  have h4 : halfBinomialCoeff 4 = -5/128 := by
    have h := halfBinomialCoeff_recurrence 3
    norm_num [h3] at h
    linarith
  exact ⟨h0, h1, h2, h3, h4⟩









end D1Bound5
end
