-- Prove2me | solution 1 for D1Bound5.finitePResidual_eq_leading_tail
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:10.387+00:00
-- url     : https://prove2.me/submissions/f70aa5b3-9374-4a71-99b4-39bfd87dfc6e

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
import Theorems.Thm_D1Bound5_finitePPairResidual_eq_leading_tail

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three































theorem finitePResidual_eq_pairs (a b s c : ℂ) (i : Fin 4) :
    finitePResidual a b s c i =
      ![finitePPairResidual a b c 0,
        finitePPairResidual a b c 0+finitePPairResidual b s c 0-finitePPairResidual a s c 0,
        finitePPairResidual a b c 1,finitePPairResidual a s c 1-finitePPairResidual b s c 1] i := by
  fin_cases i <;> simp [finitePResidual,finitePDividedMatrix,finitePPairResidual,
    finitePPairCoeff,finitePRLeft,finitePRRight,finitePTLeft,finitePTRight,
    Fin.sum_univ_succ] <;> ring

theorem _root_.solution (a b s c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (hc : c ≠ 0) (i : Fin 4) :
    finitePResidual a b s c i = finitePLeading a b s i/c^5+finitePTail a b s c i := by
  rw [finitePResidual_eq_pairs]
  simp only [finitePPairResidual_eq_leading_tail _ _ c ha hb hc,
    finitePPairResidual_eq_leading_tail _ _ c hb hs hc,
    finitePPairResidual_eq_leading_tail _ _ c ha hs hc]
  fin_cases i <;> simp [finitePLeading,finitePTail,finitePLeadingV,finitePLeadingT] <;> ring

end D1Bound5
end
