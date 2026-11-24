-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:21.278862+00:00
-- url     : https://prove2.me/submissions/4ce53aba-7dc8-45b7-b6cd-47823f1f4518

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_iff

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
theorem _root_.solution (hV2 : V2 K) (i : L) (a : Fin r) :
    vala sg S (if sg i then 0 else -1) (X (i, a) : MvPolynomial (L × Fin r) K) := by
  have h := (hV2 L sg r S).1 i a
  by_cases hs : sg i = true
  · rw [if_pos hs] at h ⊢
    rw [vala_iff, Int.ceil_zero]; exact h
  · rw [if_neg hs] at h ⊢
    have h1 : ⌈(-1 : ℝ)⌉ = -1 := by
      have := Int.ceil_intCast (R := ℝ) (-1)
      simpa using this
    rw [vala_iff, h1]; exact h
end Formalism.MainNotions.PlaneGram
