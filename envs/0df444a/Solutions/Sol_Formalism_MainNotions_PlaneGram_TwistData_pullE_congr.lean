-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.pullE_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:36.768614+00:00
-- url     : https://prove2.me/submissions/d30e7c81-fbc0-4162-978f-92db0d6b4437

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullE_apply

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
theorem _root_.solution (ζ ζ' : D.EM) (h : ∀ k a, ζ (D.e0 j k, a) = ζ' (D.e0 j k, a)) :
    D.pullE j ζ = D.pullE j ζ' := by
  ext ⟨k, a⟩
  rw [pullE_apply, pullE_apply]
  exact h k a
end Formalism.MainNotions.PlaneGram.TwistData
