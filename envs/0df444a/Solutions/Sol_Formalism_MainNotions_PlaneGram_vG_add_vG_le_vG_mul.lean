-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vG_add_vG_le_vG_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:26.479018+00:00
-- url     : https://prove2.me/submissions/dde2da69-4b33-4394-969c-6d1594b0f7c3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_vG_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vG_le_coeff

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
theorem _root_.solution (F G : MvPolynomial σ K) : vG v F + vG v G ≤ vG v (F * G) := by
  classical
  rw [le_vG_iff]
  intro γ
  rw [coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  exact add_le_add (vG_le_coeff F _) (vG_le_coeff G _)
end Formalism.MainNotions.PlaneGram
