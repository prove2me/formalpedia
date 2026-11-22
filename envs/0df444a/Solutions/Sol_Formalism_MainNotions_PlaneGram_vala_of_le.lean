-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:49.189803+00:00
-- url     : https://prove2.me/submissions/8073d943-0f8c-4cad-a211-10881d88a4d0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_mono

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
theorem _root_.solution {θ : ℝ} {L' : Type} [DecidableEq L'] {sg' : L' → Bool} {S' : Finset L'}
    {F : MvPolynomial (L × Fin r) K} {G : MvPolynomial (L' × Fin r) K}
    (h : valS sg S F ≤ valS sg' S' G) (hF : vala sg S θ F) : vala sg' S' θ G :=
  le_trans hF (toR_mono h)
end Formalism.MainNotions.PlaneGram
