-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:52:40.351698+00:00
-- url     : https://prove2.me/submissions/4faf457b-ed1a-47d8-a03d-c4e2a8c7d426

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_smul

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
variable {sg S}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {θ : ℝ} {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (-F) := by
  have := vala_smul (-1 : K) hF
  rwa [neg_smul, one_smul] at this
end Formalism.MainNotions.PlaneGram
