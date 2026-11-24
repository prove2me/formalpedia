-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_mul_left_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:20:20.260858+00:00
-- url     : https://prove2.me/submissions/6b93ee13-5da0-4427-a6f8-5be0d9bebd27

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul
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
theorem _root_.solution {θ : ℝ} {F G : MvPolynomial (L × Fin r) K} (hF : 0 ≤ valS sg S F)
    (hG : vala sg S θ G) : vala sg S θ (F * G) := by
  have := vala_mul (vala_of_nonneg hF) hG
  rwa [zero_add] at this
end Formalism.MainNotions.PlaneGram
