-- Prove2me | solution 1 for D1Bound5.finitePLeadingWeight_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:31.281444+00:00
-- url     : https://prove2.me/submissions/5bd02cb4-24a4-467a-9605-717edab62df2

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveLeading_Definitions
import Definitions.Def_D1Bound5_FinitePLeadingBound_Definitions

section
namespace D1Bound5















theorem _root_.solution (x : ℝ) (i : Fin 4) :
    finitePLeadingWeight x i =
      (∑ t, |((finitePAdaptiveLeadingTerms i t).1 : ℝ)| *
        x^(finitePLeadingRatioExponent (finitePAdaptiveLeadingTerms i t)))/256 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  fin_cases i <;> norm_num [finitePLeadingWeight,finitePAdaptiveLeadingTerms,
    finitePLeadingTerms,finitePLeadingRatioExponent,finitePLeadingNumeratorExponent,
    Fin.sum_univ_succ,Matrix.cons_val_two,h20,h21,h02,h12] <;> ring



end D1Bound5
end
