-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:03:56.03821+00:00
-- url     : https://prove2.me/submissions/38318c8b-ab28-4c6d-a122-101f4be6d798

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_add_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_iff

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
    (hG : vala sg S θ G) : vala sg S θ (F + G) := by
  rw [vala_iff] at *
  exact le_trans (le_min hF hG) (valS_add_le sg S F G)
end Formalism.MainNotions.PlaneGram
