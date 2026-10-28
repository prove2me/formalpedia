-- Prove2me | solution 1 for D1Bound5.finitePPairResidual_eq_leading_tail
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:37.863691+00:00
-- url     : https://prove2.me/submissions/40251d4f-2a75-4f97-a551-13141f0a68b8

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
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_finiteP_half_coefficients
import Theorems.Thm_D1Bound5_finiteQ_half_coefficients

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three















private theorem finiteP_sum_six (f : ℕ → ℂ) :
    (∑ m ∈ Finset.range 6, f m) = f 0+f 1+f 2+f 3+f 4+f 5 := by
  rw [Finset.sum_range_succ f 5, Finset.sum_range_succ f 4,
    Finset.sum_range_succ f 3, Finset.sum_range_succ f 2,
    Finset.sum_range_succ f 1, Finset.sum_range_succ f 0]
  simp only [Finset.sum_range_zero, zero_add]

private theorem finiteP_sum_seven (f : ℕ → ℂ) :
    (∑ m ∈ Finset.range 7, f m) = f 0+f 1+f 2+f 3+f 4+f 5+f 6 := by
  rw [Finset.sum_range_succ f 6, finiteP_sum_six]

private theorem finiteP_sum_eight (f : ℕ → ℂ) :
    (∑ m ∈ Finset.range 8, f m) = f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7 := by
  rw [Finset.sum_range_succ f 7, finiteP_sum_seven]

set_option maxHeartbeats 2000000 in
/-- The actual pair rows cancel every coefficient through c^-4. -/
theorem _root_.solution (u v c : ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0) (kind : Fin 2) :
    finitePPairResidual u v c kind =
      ![finitePLeadingR u v,finitePLeadingT u v] kind/c^5+finitePPairTail u v c kind := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := finiteQ_half_coefficients
  obtain ⟨h5,h6,h7⟩ := finiteP_half_coefficients
  fin_cases kind
  all_goals
    simp only [finitePPairResidual, finitePPairTail, finiteQHalfRemainder,
      Fin.sum_univ_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      h0,h1,h2,h3,h4,h5,h6,h7]
    norm_num [finitePPairCoeff, finitePRConstant, finitePTConstant,
      finitePRLeftCoeff, finitePRRightCoeff, finitePTLeftCoeff, finitePTRightCoeff,
      finitePairQuadratic, finitePLeadingR, finitePLeadingT]
    simp only [finiteP_sum_six, finiteP_sum_seven, finiteP_sum_eight,
      h0,h1,h2,h3,h4,h5,h6,h7]
    norm_num only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat, pow_zero, pow_one, one_mul]
    apply sub_eq_zero.mp
    ring_nf
    all_goals field_simp [hu,hv,hc] <;> ring













end D1Bound5
end
