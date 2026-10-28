-- Prove2me | solution 1 for D1Bound5.finitePAdaptiveLeading_exponents
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:40.789312+00:00
-- url     : https://prove2.me/submissions/d295d2f2-b3d7-4ccd-ad07-4b2ca04fa2fd

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













theorem _root_.solution (i : Fin 4) (t : Fin 12) :
    let u := finitePAdaptiveLeadingTerms i t
    let p := finitePLeadingNumeratorExponent u
    p 0+p 1+p 2+3 ≤ u.2.2.2.2+2 ∧
      finitePLeadingRatioExponent u+p 1+p 2 = (if u.2.1=0 then 2 else u.2.2.2.2+2) ∧
      (u.2.1 ≠ 2 → p 2 ≤ 2) := by
  fin_cases i <;> fin_cases t <;>
    norm_num [finitePAdaptiveLeadingTerms,finitePLeadingTerms,
      finitePLeadingNumeratorExponent,finitePLeadingRatioExponent,Fin.ext_iff,
      Matrix.cons_val_two] <;> decide





end D1Bound5
end
