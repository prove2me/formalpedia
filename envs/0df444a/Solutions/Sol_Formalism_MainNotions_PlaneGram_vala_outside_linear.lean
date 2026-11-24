-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_outside_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:30.438434+00:00
-- url     : https://prove2.me/submissions/52e248da-2d4c-4021-8106-6494a90d2232

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_outside_linear
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
theorem _root_.solution {θ : ℝ}
    (Φ : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (out : L → Prop) [DecidablePred out] (hout : ∀ i ∈ S, ¬ out i)
    (h1 : ∀ α, Φ (monomial α 1) = monomial (eIn out α) 1 * Φ (monomial (eOut out α) 1))
    (h2 : ∀ α, 0 ≤ valS sg S (Φ (monomial (eOut out α) 1))) {F : MvPolynomial (L × Fin r) K}
    (hF : vala sg S θ F) : vala sg S θ (Φ F) :=
  vala_of_le (valS_outside_linear out sg S Φ hout h1 h2 F) hF
end Formalism.MainNotions.PlaneGram
