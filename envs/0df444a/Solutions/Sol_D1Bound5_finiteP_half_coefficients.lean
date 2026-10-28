-- Prove2me | solution 1 for D1Bound5.finiteP_half_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:38.595682+00:00
-- url     : https://prove2.me/submissions/bb321e7a-8f0e-484f-9ea1-184e3803b20c

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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_finiteQ_half_coefficients
import Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem _root_.solution :
    halfBinomialCoeff 5 = 7/256 ∧ halfBinomialCoeff 6 = -21/1024 ∧
    halfBinomialCoeff 7 = 33/2048 := by
  have h4 := finiteQ_half_coefficients.2.2.2.2
  have h5 : halfBinomialCoeff 5 = 7/256 := by
    have h := halfBinomialCoeff_recurrence 4
    norm_num [h4] at h
    linarith
  have h6 : halfBinomialCoeff 6 = -21/1024 := by
    have h := halfBinomialCoeff_recurrence 5
    norm_num [h5] at h
    linarith
  have h7 : halfBinomialCoeff 7 = 33/2048 := by
    have h := halfBinomialCoeff_recurrence 6
    norm_num [h6] at h
    linarith
  exact ⟨h5,h6,h7⟩

































end D1Bound5
end
