-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_monomial_nonneg_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:39.180011+00:00
-- url     : https://prove2.me/submissions/2c0db8cc-8f80-4475-bafa-98f4526dc459

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_nonneg_of_free

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
variable {K : Type} [Field K]
variable {L : Type} [DecidableEq L] {r : ℕ} {sg : L → Bool} {S : Finset L}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (μ : L × Fin r →₀ ℕ) (c : K) (h : ∀ i ∈ S, ∀ a, μ (i, a) = 0) :
    0 ≤ valS sg S (monomial μ c) := by
  classical
  refine valS_nonneg_of_free sg S _ fun α hα i hi a => ?_
  have : α = μ := by
    have := support_monomial_subset hα
    simpa using this
  rw [this]; exact h i hi a
end Formalism.MainNotions.PlaneGram
