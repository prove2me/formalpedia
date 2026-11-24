-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:04.387235+00:00
-- url     : https://prove2.me/submissions/fa12c500-cd53-4fd3-b369-efd8df6bd3f3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_C_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_of_nonneg

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
theorem _root_.solution : vala sg S 0 (1 : MvPolynomial (L × Fin r) K) := by
  have := valS_C_nonneg sg S (1 : K) (r := r)
  rw [map_one] at this
  exact vala_of_nonneg this
end Formalism.MainNotions.PlaneGram
