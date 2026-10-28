-- Prove2me | solution 1 for D1Bound5.finitePTailCoeffTerms_admissible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:50.826097+00:00
-- url     : https://prove2.me/submissions/a99a214a-3431-4c92-9baa-af9b3dc1d513

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
import Definitions.Def_D1Bound5_FinitePTailCoefficients_Definitions

section
namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three





theorem _root_.solution (kind side : Fin 2) (l t : Fin 3) :
    (finitePTailCoeffTerms kind side l t).2.2 ≤ 2 ∧
      (finitePTailCoeffTerms kind side l t).2.1+
        (finitePTailCoeffTerms kind side l t).2.2 ≤ 3+(l : ℕ) := by
  fin_cases kind <;> fin_cases side <;> fin_cases l <;> fin_cases t <;> decide







end D1Bound5
end
