-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.seven_lt_lstar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:46.349299+00:00
-- url     : https://prove2.me/submissions/00e87b2e-10b8-46b1-a89c-9cae1d69957b

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_div_lstar_pos
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_eta_nonneg__1aa77f39dc77

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
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) : 7 < P.lstar := by
  have h2 := H.win_lt
  have hη := eta_nonneg' H
  have hbl := b_div_lstar_pos H G
  have ht : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have e : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
