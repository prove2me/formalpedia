-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.costBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:57.036216+00:00
-- url     : https://prove2.me/submissions/a626ad9f-502a-4004-be4c-5b5f0ad04cf9

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_ex_mul_log_le_of_thickA
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_ex_mul_log_le_of_thinA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : CostB := by
  intro P H G ι _ D hcard hA hK hW l hl
  rw [Finset.sum_mul]
  calc ∑ τ, (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ ∑ _τ : ι, (P.Nr : ℝ) ^ 2 * P.L := by
        apply Finset.sum_le_sum
        intro τ _
        by_cases hτ : τ ∈ D.T2
        · exact ex_mul_log_le_of_thickA H G hK hτ hl
        · exact ex_mul_log_le_of_thinA H G hA hW hτ hl
    _ = (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L := by
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        ring
end Formalism.CohomologicalDescent.LogSmallConstantBounds
