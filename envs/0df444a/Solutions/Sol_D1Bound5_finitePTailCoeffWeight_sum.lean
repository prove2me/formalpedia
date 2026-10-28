-- Prove2me | solution 1 for D1Bound5.finitePTailCoeffWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:52:57.824344+00:00
-- url     : https://prove2.me/submissions/ab86a88b-7a39-4448-b3b7-4d0a2288332b

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







theorem _root_.solution (kind : Fin 2) :
    (∑ side : Fin 2, ∑ l : Fin 3, finitePTailCoeffWeight kind side l) =
      ![876,2676] kind := by
  fin_cases kind <;> decide





end D1Bound5
end
