-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vG_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:31.882915+00:00
-- url     : https://prove2.me/submissions/5b3f845c-e896-41cc-b87f-e387edea0183

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v}
variable {σ τ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution : vG v (0 : MvPolynomial σ K) = ⊤ := by
  simp [vG]
end Formalism.MainNotions.PlaneGram
