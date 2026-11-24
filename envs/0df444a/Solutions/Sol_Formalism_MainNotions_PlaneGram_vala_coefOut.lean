-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_coefOut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:43.15573+00:00
-- url     : https://prove2.me/submissions/1a6552c7-e380-42e3-bd28-e488197475b4

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_coefOut_le
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
theorem _root_.solution {θ : ℝ} (out : L → Prop) [DecidablePred out] (hout : ∀ i ∈ S, ¬ out i)
    (μ : L × Fin r →₀ ℕ) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (coefOut out μ F) := vala_of_le (valS_coefOut_le out sg S hout μ F) hF
end Formalism.MainNotions.PlaneGram
