-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:03:56.719598+00:00
-- url     : https://prove2.me/submissions/b5bb9339-1806-4881-836b-363f45d5785a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_mul_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_add

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
theorem _root_.solution {θ₁ θ₂ : ℝ} {F G : MvPolynomial (L × Fin r) K} (hF : vala sg S θ₁ F)
    (hG : vala sg S θ₂ G) : vala sg S (θ₁ + θ₂) (F * G) := by
  unfold vala at *
  refine le_trans ?_ (toR_mono (valS_mul_le sg S F G))
  rw [toR_add, WithTop.coe_add]
  exact add_le_add hF hG
end Formalism.MainNotions.PlaneGram
