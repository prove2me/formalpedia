-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:03.34581+00:00
-- url     : https://prove2.me/submissions/1c515e17-d58c-47aa-beb1-f1badc33cf0b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_toR_iff

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
theorem _root_.solution (θ : ℝ) (F : MvPolynomial (L × Fin r) K) :
    vala sg S θ F ↔ ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤ valS sg S F := le_toR_iff θ _
end Formalism.MainNotions.PlaneGram
