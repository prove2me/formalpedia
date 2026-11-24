-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.block_height_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:04:48.93581+00:00
-- url     : https://prove2.me/submissions/198433ec-fe95-4cea-a4fb-ce5259f41f5b

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_blockTriangular_of_mul_eq_pow_smul_one
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_toSquareBlock_mul_of_blockTriangular_alt

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
theorem _root_.solution : BlockHeight := by
  intro R _ _ π n h Φ Φ' b hπ hΦ hm
  have hΦ' := blockTriangular_of_mul_eq_pow_smul_one π n h Φ Φ' b hπ hΦ hm
  refine ⟨hΦ', fun r => ?_⟩
  rw [← toSquareBlock_mul_of_blockTriangular_alt Φ Φ' b hΦ hΦ' r, hm]
  ext ⟨i, hi⟩ ⟨j, hj⟩
  by_cases hij : i = j
  · subst hij; simp [Matrix.toSquareBlock_def]
  · simp [Matrix.toSquareBlock_def, Matrix.one_apply, hij]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
