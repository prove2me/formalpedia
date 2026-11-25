-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.lJDenom_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:49:12.060785+00:00
-- url     : https://prove2.me/submissions/d77e77bb-07ff-497a-8c1d-2165311a8b14

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_three_mul_h_pos_le

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
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) : 0 < indexDenominator P := by
  have nb := natBounds H
  obtain ⟨c1, _⟩ := log_three_mul_h_pos_le H G
  unfold indexDenominator
  exact mul_pos (mul_pos (by linarith [nb.k1]) (by linarith [nb.m1, nb.t6])) c1
end Formalism.CohomologicalDescent.LogSmallConstantBounds
