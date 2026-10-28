-- Prove2me | solution 1 for D1Bound5.mixedFourEnvelope_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:34.405735+00:00
-- url     : https://prove2.me/submissions/5f3975b3-7922-4738-8825-2a983d4ce042

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_WeightedRowCertificate_Definitions

section
namespace D1Bound5









theorem _root_.solution (i j : Fin 4) :
    mixedFourEnvelope i j = mixedFourEnvelope j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    change (if i = j then (0 : ℝ) else if i = 0 ∨ j = 0 then 1 / 18 else 1 / 64) =
      (if j = i then (0 : ℝ) else if j = 0 ∨ i = 0 then 1 / 18 else 1 / 64)
    rw [if_neg h, if_neg h']
    by_cases k : i = 0 ∨ j = 0
    · rw [if_pos k, if_pos (by tauto)]
    · rw [if_neg k, if_neg (by tauto)]





end D1Bound5

namespace D1Bound5





end D1Bound5
end
