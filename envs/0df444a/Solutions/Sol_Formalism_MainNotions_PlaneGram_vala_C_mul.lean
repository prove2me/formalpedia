-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:51.95456+00:00
-- url     : https://prove2.me/submissions/258fcf59-0886-4e8a-9b3c-e337647fbf0b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_C_mul_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_of_le

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
theorem _root_.solution {θ : ℝ} (a : K) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (C a * F) := vala_of_le (valS_C_mul_le sg S a F) hF
end Formalism.MainNotions.PlaneGram
