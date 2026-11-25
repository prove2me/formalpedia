-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:18:14.905355+00:00
-- url     : https://prove2.me/submissions/fb9e6008-5a25-4947-ba19-cf3dbfcaadb9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_neg

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
theorem _root_.solution {θ : ℝ} {F G : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F)
    (hG : vala sg S θ G) : vala sg S θ (F - G) := by
  rw [sub_eq_add_neg]; exact vala_add hF (vala_neg hG)
end Formalism.MainNotions.PlaneGram
