-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:26.06067+00:00
-- url     : https://prove2.me/submissions/6684a879-7858-4ace-90b9-bbb5316ead52

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff_pge

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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution : valS sg S (0 : MvPolynomial (L × Fin r) K) = ⊤ := by
  rw [eq_top_iff, le_valS_iff_pge, map_zero]; exact pge_zero _
end Formalism.MainNotions.PlaneGram
