-- Prove2me | solution 1 for D1Bound5.mixedFour_entry_norm_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:31.037895+00:00
-- url     : https://prove2.me/submissions/f711945a-eec0-4423-b64d-83153cde0d53

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















end D1Bound5

namespace D1Bound5

/-- Any complex matrix obeying the mixed first-row and lower-block entry
bounds is entrywise dominated by the exact rational envelope. -/
theorem _root_.solution
    (E : Matrix (Fin 4) (Fin 4) ℂ)
    (hdiag : ∀ i, E i i = 0)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖E i j‖ < (1 / 18 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖E i j‖ < (1 / 64 : ℝ))
    (i j : Fin 4) :
    ‖E i j‖ ≤ mixedFourEnvelope i j := by
  by_cases hij : i = j
  · subst j
    simp [mixedFourEnvelope, hdiag]
  · by_cases hzero : i = 0 ∨ j = 0
    · simpa [mixedFourEnvelope, hij, hzero] using
        (le_of_lt (hfirst i j hij hzero))
    · simpa [mixedFourEnvelope, hij, hzero] using
        (le_of_lt (hlater i j hij hzero))



end D1Bound5
end
