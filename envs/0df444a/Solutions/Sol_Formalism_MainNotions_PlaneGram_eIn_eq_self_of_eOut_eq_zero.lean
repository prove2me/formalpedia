-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.eIn_eq_self_of_eOut_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:28.621233+00:00
-- url     : https://prove2.me/submissions/e3bd3ff2-6208-4756-834b-b5c39215f68b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add_eIn

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
theorem _root_.solution {α : L × Fin r →₀ ℕ} (h : eOut out α = 0) : eIn out α = α := by
  have := eOut_add_eIn out α
  rwa [h, zero_add] at this
end Formalism.MainNotions.PlaneGram
