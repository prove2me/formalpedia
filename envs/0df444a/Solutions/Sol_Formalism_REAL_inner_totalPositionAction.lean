-- Prove2me | solution 1 for Formalism.REAL.inner_totalPositionAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:16.80703+00:00
-- url     : https://prove2.me/submissions/4cf14a17-c2b7-485b-939c-c38c0e670591

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_inner_positionAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (c d : Fin n) (F G : Arr V n j) :
    ⟪positionsE V n j c d F, G⟫_ℂ = ⟪F, positionsE V n j d c G⟫_ℂ := by
  simp only [positionsE, LinearMap.sum_apply, sum_inner, inner_sum, inner_positionAction]
end Formalism.REAL
