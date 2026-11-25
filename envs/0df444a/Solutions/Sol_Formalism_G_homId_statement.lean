-- Prove2me | solution 1 for Formalism.G.homId_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:56:06.203062+00:00
-- url     : https://prove2.me/submissions/d50bc12e-9828-4450-9d7a-64e395df7bb9

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.G
namespace Formalism.G
theorem _root_.solution : HomId := by
  unfold HomId
  intro R _ F
  refine ⟨by simp, ?_⟩
  rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff)]
  have hXY : ![atX (PowerSeries.X : PowerSeries R), atY PowerSeries.X] = MvPowerSeries.X := by
    funext s
    fin_cases s <;> simp [atX, atY, PowerSeries.subst_X (PowerSeries.HasSubst.X _)]
  rw [hXY, MvPowerSeries.subst_self]
  rfl
end Formalism.G
