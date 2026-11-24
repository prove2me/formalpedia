-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_superset_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:28.039893+00:00
-- url     : https://prove2.me/submissions/368fa7c8-8965-4fa8-a3c9-cf4dd6c4e4d3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
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
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hV2 : V2 K) {θ : ℝ} {S' : Finset L} (hsub : S ⊆ S')
    (hvec : ∀ i ∈ S', i ∉ S → sg i = true) {F : MvPolynomial (L × Fin r) K}
    (hF : vala sg S θ F) : vala sg S' θ F :=
  vala_of_le ((hV2 L sg r S).2.2.1 S' hsub hvec F) hF
end Formalism.MainNotions.PlaneGram
