-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.dg_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:36.699548+00:00
-- url     : https://prove2.me/submissions/fcaed613-31a7-48e5-bdff-4ed7117a92ad

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_dg


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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} {f g : (σ →₀ ℕ) → K} {F : MvPolynomial σ K}
    (h : ∀ α ∈ F.support, f α = g α) : dg f F = dg g F := by
  ext β
  simp only [coeff_dg]
  by_cases hβ : β ∈ F.support
  · rw [h β hβ]
  · rw [notMem_support_iff.mp hβ, mul_zero, mul_zero]
end Formalism.MainNotions.PlaneGram
