-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.lstarDenom_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:04:48.227833+00:00
-- url     : https://prove2.me/submissions/ea033b02-8d3f-4fd6-bdb6-a13f613c8fed

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_le_lstarDenom

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
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) : 0 < lstarDenom P := by
  have nb := natBounds H
  have hL := G.L_ge
  have : (0 : ℝ) < (P.t : ℝ) ^ 3 * P.L ^ 2 :=
    mul_pos (pow_pos (by linarith [nb.t6]) 3) (pow_pos (by linarith) 2)
  exact lt_of_lt_of_le this (le_lstarDenom H G)
end Formalism.CohomologicalDescent.LogSmallConstantBounds
