-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:30.386982+00:00
-- url     : https://prove2.me/submissions/63e38aa2-83b4-4f0f-ad64-74e750324169

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_one

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
theorem _root_.solution {θ : ℝ} {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) (k : ℕ) :
    vala sg S (k * θ) (F ^ k) := by
  induction k with
  | zero => simpa using vala_one
  | succ k ih =>
    rw [pow_succ]
    have := vala_mul ih hF
    convert this using 1
    push_cast; ring
end Formalism.MainNotions.PlaneGram
