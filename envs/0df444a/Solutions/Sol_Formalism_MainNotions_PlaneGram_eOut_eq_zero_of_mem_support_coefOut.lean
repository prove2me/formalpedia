-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.eOut_eq_zero_of_mem_support_coefOut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:15.071637+00:00
-- url     : https://prove2.me/submissions/1e79e957-e4d4-48c6-8528-d828048ff6b2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_coefOut

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {μ β : L × Fin r →₀ ℕ} {F : MvPolynomial (L × Fin r) K}
    (h : β ∈ (coefOut out μ F).support) : eOut out β = 0 := by
  rw [mem_support_iff, coeff_coefOut] at h
  by_contra h0
  exact h (if_neg fun hh => h0 hh.1)
end Formalism.MainNotions.PlaneGram
