-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.pullE_eIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:42.304928+00:00
-- url     : https://prove2.me/submissions/351dff4d-75c8-4a2e-8219-bf25565c98a3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullE_congr
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_apply


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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ζ : D.EM) : D.pullE j (eIn (D.outSeg j) ζ) = D.pullE j ζ := by
  apply D.pullE_congr j
  intro k a
  have hout : ¬ D.outSeg j (D.e0 j k) := fun h => h ⟨k, rfl⟩
  exact (eIn_apply (out := D.outSeg j) ζ (D.e0 j k, a)).trans (if_neg hout)
end Formalism.MainNotions.PlaneGram.TwistData
