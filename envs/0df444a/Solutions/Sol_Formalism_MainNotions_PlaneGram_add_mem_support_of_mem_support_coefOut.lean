-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.add_mem_support_of_mem_support_coefOut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:18:09.046131+00:00
-- url     : https://prove2.me/submissions/7922ce06-e0d9-4521-8970-0495a74ca1de

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
theorem _root_.solution {μ β : L × Fin r →₀ ℕ}
    {F : MvPolynomial (L × Fin r) K} (h : β ∈ (coefOut out μ F).support) : μ + β ∈ F.support := by
  rw [mem_support_iff, coeff_coefOut] at h
  rw [mem_support_iff]
  intro h0
  apply h
  split_ifs
  · exact h0
  · rfl
end Formalism.MainNotions.PlaneGram
