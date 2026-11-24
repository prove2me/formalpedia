-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:49:07.873056+00:00
-- url     : https://prove2.me/submissions/c6402a9e-462d-4dac-a115-33ff3ffe3e67

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff_pge
import Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_valS

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
theorem _root_.solution (F G : MvPolynomial (L × Fin r) K) :
    min (valS sg S F) (valS sg S G) ≤ valS sg S (F + G) := by
  rw [le_valS_iff_pge, map_add]
  exact pge_add (pge_mono (min_le_left _ _) (pge_valS sg S F))
    (pge_mono (min_le_right _ _) (pge_valS sg S G))
end Formalism.MainNotions.PlaneGram
