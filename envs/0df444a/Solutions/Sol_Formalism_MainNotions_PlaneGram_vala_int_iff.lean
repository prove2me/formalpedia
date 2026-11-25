-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:18:03.161818+00:00
-- url     : https://prove2.me/submissions/f535b3d3-57a3-442c-9029-1f83bfcc4111

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_iff_Aset

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
theorem _root_.solution (n : ℤ) (F : MvPolynomial (L × Fin r) K) :
    vala sg S (n : ℝ) F ↔ F ∈ Aset sg S n := by
  rw [vala_iff_Aset, Int.ceil_intCast]
end Formalism.MainNotions.PlaneGram
