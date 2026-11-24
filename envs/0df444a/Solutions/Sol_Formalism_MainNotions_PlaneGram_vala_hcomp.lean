-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_hcomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:45:18.877097+00:00
-- url     : https://prove2.me/submissions/6f9a2d67-34b9-43b1-8199-713a62e76d0c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_hcomp_le
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
theorem _root_.solution [Fintype L] {θ : ℝ} (d : L → ℕ) {F : MvPolynomial (L × Fin r) K}
    (hF : vala sg S θ F) : vala sg S θ (hcomp d F) := vala_of_le (valS_hcomp_le sg S d F) hF
end Formalism.MainNotions.PlaneGram
