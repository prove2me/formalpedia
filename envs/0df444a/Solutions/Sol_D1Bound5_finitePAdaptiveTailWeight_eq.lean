-- Prove2me | solution 1 for D1Bound5.finitePAdaptiveTailWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:33.032972+00:00
-- url     : https://prove2.me/submissions/87e49619-a42b-4fbb-aaed-d1dcfe492cc7

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
import Definitions.Def_D1Bound5_FinitePAdaptiveTailData_Definitions
import Definitions.Def_D1Bound5_FinitePHeight_Definitions

section
namespace D1Bound5





/-- The four positive polynomials are computed from the actual integer
coefficient lists after the H and V cancellations. -/
theorem _root_.solution (i : Fin 4) (x : ℝ) :
    finitePAdaptiveTailWeight i x =
      ![295*x+143*x^2+143*x^4+295*x^5,
        590*(x+x^4+x^5),
        885+1144*x+435*x^2+42*x^3+170*x^4,
        885+1144*x+435*x^2+2634*x^3+170*x^4] i := by
  fin_cases i <;>
    norm_num [finitePAdaptiveTailWeight,finitePAdaptiveTailExponent,
      finitePRootTerms,Fin.sum_univ_succ] <;> ring





end D1Bound5
end
