-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_of_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:10.221926+00:00
-- url     : https://prove2.me/submissions/ddc367a2-a991-4995-a744-97970d562a9d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_coe
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
theorem _root_.solution {θ : ℝ} (k : ℤ) {F G : MvPolynomial (L × Fin r) K}
    (h : valS sg S F + ((k : ℤ) : WithTop ℤ) ≤ valS sg S G) (hF : vala sg S θ F) :
    vala sg S (θ + k) G := by
  unfold vala at *
  refine le_trans ?_ (toR_mono h)
  rw [toR_add, toR_coe, WithTop.coe_add]
  exact add_le_add hF le_rfl
end Formalism.MainNotions.PlaneGram
