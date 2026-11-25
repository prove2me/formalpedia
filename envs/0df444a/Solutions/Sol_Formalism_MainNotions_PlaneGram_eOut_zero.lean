-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.eOut_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:14.353273+00:00
-- url     : https://prove2.me/submissions/727d3775-2e76-4625-b321-7c6e025241f8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution : eOut out (0 : L × Fin r →₀ ℕ) = 0 := by
  ext x; simp [eOut_apply]
end Formalism.MainNotions.PlaneGram
