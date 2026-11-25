-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.support_dg_subset_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:44.024846+00:00
-- url     : https://prove2.me/submissions/646fe32a-c759-4faa-9e72-3482af481ca5

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
theorem _root_.solution {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    (dg f F).support ⊆ F.support := by
  intro β hβ
  rw [mem_support_iff, coeff_dg] at hβ
  rw [mem_support_iff]
  intro h0; apply hβ; rw [h0, mul_zero]
end Formalism.MainNotions.PlaneGram
