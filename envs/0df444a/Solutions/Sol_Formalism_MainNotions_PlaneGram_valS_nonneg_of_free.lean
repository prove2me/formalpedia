-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_nonneg_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:36:35.463403+00:00
-- url     : https://prove2.me/submissions/045c42c8-946a-40b5-81a2-5db17ae7b677

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_nonneg_of_vecS

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
variable {K : Type} [Field K]
variable {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ i ∈ S, ∀ a, α (i, a) = 0) : 0 ≤ valS sg S F :=
  valS_nonneg_of_vecS sg S F fun α hα i a hne hi => absurd (h α hα i hi a) hne
end Formalism.MainNotions.PlaneGram
