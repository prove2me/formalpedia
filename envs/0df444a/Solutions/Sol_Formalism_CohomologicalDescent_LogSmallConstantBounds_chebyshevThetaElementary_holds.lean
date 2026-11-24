-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.chebyshevThetaElementary_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:53.212222+00:00
-- url     : https://prove2.me/submissions/7d27292a-1f63-4d5b-a6ef-4c3c3f41d230

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_pr_eq_primesUpTo_floor
import Theorems.Thm_Formalism_RankGapBounds_ChebyshevFactorialBounds_chebyshevThetaLe_holds


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
theorem _root_.solution : ConvolutionKernelIntegrable := by
  intro y hy
  rw [pr_eq_primesUpTo_floor]
  have h := Formalism.RankGapBounds.ChebyshevFactorialBounds.chebyshevThetaLe_holds ⌊y⌋₊
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  exact h.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hy) h4)
end Formalism.CohomologicalDescent.LogSmallConstantBounds
