-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_ddiv_letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:05.0088+00:00
-- url     : https://prove2.me/submissions/0fd6c009-343d-4e1e-a64a-70e7e974267e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mono
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vala_ddiv_letter__58971d2a3a04

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
theorem _root_.solution (hV2 : V2 K) {θ : ℝ} (i : L) (β : Fin r →₀ ℕ)
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S (θ - absE β) (ddiv (onLetter i β) F) := by
  refine vala_mono ?_ (vala_ddiv_letter' hV2 i β hF)
  split_ifs
  · exact le_rfl
  · have : (0 : ℝ) ≤ absE β := Nat.cast_nonneg _
    linarith
end Formalism.MainNotions.PlaneGram
