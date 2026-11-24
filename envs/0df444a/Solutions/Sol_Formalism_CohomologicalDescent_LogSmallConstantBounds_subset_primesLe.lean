-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.subset_primesLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:37.507647+00:00
-- url     : https://prove2.me/submissions/b78d60c8-864c-44ac-9f8f-624b83dbbc16

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_mem_primesLe

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
theorem _root_.solution {y : ℝ} (hy : 0 ≤ y) {Q : Finset ℕ} (hQ : ∀ l ∈ Q, l.Prime ∧ (l : ℝ) ≤ y) :
    Q ⊆ pr y := fun l hl => (mem_primesLe hy).2 (hQ l hl)
end Formalism.CohomologicalDescent.LogSmallConstantBounds
