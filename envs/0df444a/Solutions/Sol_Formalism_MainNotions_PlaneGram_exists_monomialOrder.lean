-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.exists_monomialOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:42.659138+00:00
-- url     : https://prove2.me/submissions/f45d4434-3266-46cc-bedc-03a4e457c5ff

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
theorem _root_.solution (σ : Type) : Nonempty (MonomialOrder.{0, 0} σ) := by
  obtain ⟨lo, wf⟩ := exists_wellFoundedLT σ
  let _ : LinearOrder σ := @OrderDual.instLinearOrder σ lo
  have : WellFoundedGT σ := ⟨wf.wf⟩
  exact ⟨MonomialOrder.lex⟩
end Formalism.MainNotions.PlaneGram
