-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.toSquareBlock_mul_of_blockTriangular_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:10.988388+00:00
-- url     : https://prove2.me/submissions/6c549e69-1ed2-4bb5-af71-2e8c01d28278

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (b : Fin n → ℕ) (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (r : ℕ) :
    (A * B).toSquareBlock b r = A.toSquareBlock b r * B.toSquareBlock b r := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.toSquareBlock_def, Matrix.toBlock_apply, Matrix.mul_apply,
    Matrix.of_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => b k = r)]
  have hz : ∑ k : {k // ¬ b k = r}, A i k * B k j = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨k, hk⟩ -
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA (by rw [hi]; exact h), zero_mul]
    · rw [hB (by rw [hj]; exact h), mul_zero]
  rw [hz, add_zero]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
