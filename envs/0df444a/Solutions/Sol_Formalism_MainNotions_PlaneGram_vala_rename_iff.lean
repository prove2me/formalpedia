-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_rename_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:55:27.4548+00:00
-- url     : https://prove2.me/submissions/575e2be0-439c-4f30-99ea-79f47b0b09a2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_rename

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
theorem _root_.solution {L' : Type} [DecidableEq L'] (f : L → L') (hf : Function.Injective f)
    (sg' : L' → Bool) (S' : Finset L') (θ : ℝ) (F : MvPolynomial (L × Fin r) K) :
    vala sg' S' θ (rename (Prod.map f id) F) ↔ vala (sg' ∘ f) (S'.preimage f hf.injOn) θ F := by
  unfold vala; rw [valS_rename f hf]
end Formalism.MainNotions.PlaneGram
