-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:03.585012+00:00
-- url     : https://prove2.me/submissions/1483e972-067e-474b-b3d5-f7094eff3613

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_top

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
theorem _root_.solution (θ : ℝ) : vala sg S θ (0 : MvPolynomial (L × Fin r) K) := by
  unfold vala; rw [valS_zero, toR_top]; exact le_top
end Formalism.MainNotions.PlaneGram
