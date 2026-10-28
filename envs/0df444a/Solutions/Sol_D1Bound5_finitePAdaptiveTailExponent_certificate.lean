-- Prove2me | solution 1 for D1Bound5.finitePAdaptiveTailExponent_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:32.84685+00:00
-- url     : https://prove2.me/submissions/57215007-8d94-4112-8dae-56deb58d0246

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







/-- Every concrete term meets the exponent inequalities used by the
adaptive scalar estimate. Zero padding also satisfies these inequalities. -/
theorem _root_.solution (i : Fin 4) (l j t : Fin 3) :
    let u := finitePRootTerms i l j t
    u.2.1+u.2.2.1+u.2.2.2+3 ≤ (4+(l : ℕ))+2 ∧
    (j=0 → finitePAdaptiveTailExponent i l j t+u.2.2.1+u.2.2.2=2) ∧
    (j=1 → finitePAdaptiveTailExponent i l j t+u.2.2.1+u.2.2.2=(4+(l : ℕ))+2 ∧
      u.2.2.2 ≤ 2) ∧
    (j=2 → finitePAdaptiveTailExponent i l j t+u.2.2.1+u.2.2.2=(4+(l : ℕ))+2) := by
  fin_cases i <;> fin_cases l <;> fin_cases j <;> fin_cases t <;>
    norm_num [finitePAdaptiveTailExponent,finitePRootTerms] <;> decide



end D1Bound5
end
