-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.integral_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:38.586513+00:00
-- url     : https://prove2.me/submissions/8952204a-0069-4069-9e63-4a4d7d0214d0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_vG_iff

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
theorem _root_.solution (F : MvPolynomial σ K) : Integral v F ↔ 0 ≤ vG v F :=
  (le_vG_iff F 0).symm
end Formalism.MainNotions.PlaneGram
