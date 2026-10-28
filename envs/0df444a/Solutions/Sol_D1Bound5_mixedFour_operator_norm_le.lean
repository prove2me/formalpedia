-- Prove2me | solution 1 for D1Bound5.mixedFour_operator_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:34:22.735559+00:00
-- url     : https://prove2.me/submissions/2d1010b8-f66c-4026-8cc8-99a1cab261f7

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
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
import Theorems.Thm_D1Bound5_mixedFourEnvelope_symmetric
import Theorems.Thm_D1Bound5_mixedFour_entry_norm_le_envelope
import Theorems.Thm_D1Bound5_weightedSchur_four_opNorm

section
namespace D1Bound5





theorem weightedFourWeights_pos (i : Fin 4) : 0 < weightedFourWeights i := by
  fin_cases i <;> norm_num [weightedFourWeights]

theorem mixedFourEnvelope_nonneg (i j : Fin 4) : 0 ≤ mixedFourEnvelope i j := by
  unfold mixedFourEnvelope
  split_ifs <;> norm_num



/-- Exact weighted-row certificate for the mixed product-four branch. -/
theorem mixedFourEnvelope_weighted_rows (i : Fin 4) :
    (∑ j : Fin 4, mixedFourEnvelope i j * weightedFourWeights j) ≤
      (11 / 96 : ℝ) * weightedFourWeights i := by
  fin_cases i <;>
    (norm_num [Fin.sum_univ_four, mixedFourEnvelope, weightedFourWeights] <;>
      simp <;> norm_num)



end D1Bound5

namespace D1Bound5





end D1Bound5
end

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5



end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5



/-- The concrete mixed 4x4 weighted Schur operator-norm estimate needed
in the A >= 1, B >= 3 branch of manuscript Lemma product-four. -/
theorem _root_.solution
    (E : Matrix (Fin 4) (Fin 4) ℂ)
    (hdiag : ∀ i, E i i = 0)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖E i j‖ < (1 / 18 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖E i j‖ < (1 / 64 : ℝ)) :
    ‖E‖ ≤ (11 / 96 : ℝ) := by
  exact weightedSchur_four_opNorm E mixedFourEnvelope weightedFourWeights
    (11 / 96) mixedFourEnvelope_nonneg weightedFourWeights_pos
    (by norm_num) mixedFourEnvelope_symmetric mixedFourEnvelope_weighted_rows
    (mixedFour_entry_norm_le_envelope E hdiag hfirst hlater)

end D1Bound5
end
