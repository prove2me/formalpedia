-- Prove2me | solution 1 for D1Bound5.mixedAdjEnvelope_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:58.345086+00:00
-- url     : https://prove2.me/submissions/21f3e8a5-95ed-493b-bd8d-7251ca9d4e83

import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_MixedAdjugateEnvelope_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





theorem _root_.solution (i j : Fin 4) :
    mixedAdjEnvelope i j = mixedAdjEnvelope j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    change (if i = j then (if i = 0 then (1/40 : ℝ) else 7/100)
      else if i = 0 ∨ j = 0 then 53/1000 else 47/1000) =
      (if j = i then (if j = 0 then (1/40 : ℝ) else 7/100)
      else if j = 0 ∨ i = 0 then 53/1000 else 47/1000)
    rw [if_neg h, if_neg h']
    by_cases hz : i = 0 ∨ j = 0
    · rw [if_pos hz, if_pos (by tauto)]
    · rw [if_neg hz, if_neg (by tauto)]





end D1Bound5
end
