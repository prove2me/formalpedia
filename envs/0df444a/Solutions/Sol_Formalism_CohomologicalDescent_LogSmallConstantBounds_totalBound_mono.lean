-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.totalBound_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:47:03.383617+00:00
-- url     : https://prove2.me/submissions/b83365d6-9930-4a01-88cb-6d0d72282236

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds

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
theorem _root_.solution (P : Par) (T : ℕ) {X Y : ℝ} (h : X ≤ Y) : totalBound P T X ≤ totalBound P T Y := by
  unfold totalBound
  have := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
