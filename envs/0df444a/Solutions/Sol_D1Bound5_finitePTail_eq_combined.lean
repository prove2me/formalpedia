-- Prove2me | solution 1 for D1Bound5.finitePTail_eq_combined
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:07.997158+00:00
-- url     : https://prove2.me/submissions/681cb05d-faf1-410f-bad9-59d2a2bc5ccc

import Lean.Elab.Tactic.Omega
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePHeight_Definitions
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions

section
namespace D1Bound5









set_option maxHeartbeats 4000000 in
/-- Combine the actual Taylor tails before applying the triangle inequality.
In particular the shared s-column terms in H and V cancel here. -/
theorem _root_.solution (a b s c : ℂ) (i : Fin 4) :
    finitePTail a b s c i =
      ∑ j : Fin 3, ∑ l : Fin 3, ![a,b,s] j*finitePRootCoeff a b s i l j*c^(l : ℕ)*
        finiteQHalfRemainder (6+(l : ℕ)) (1/(![a,b,s] j*c)) := by
  fin_cases i
  all_goals
    norm_num [finitePTail,finitePPairTail,finitePRootCoeff,finitePRootTerms,
      finitePTermValue,finitePPairCoeff,finitePRLeftCoeff,finitePRRightCoeff,
      finitePTLeftCoeff,finitePTRightCoeff,Fin.sum_univ_succ]
    <;> ring

end D1Bound5
end
