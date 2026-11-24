-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.integral_prod_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:55:26.600808+00:00
-- url     : https://prove2.me/submissions/49dc9f9e-10dc-48a8-8d5f-fd23ce010f06

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Theorems.Thm_Formalism_MainNotions_PlaneGram_integral_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vG_prod
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vG_rename

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v}
variable {σ τ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {ι : Type} [Fintype ι] (col : ι → MvPolynomial σ K) (f : ι → σ → τ)
    (hf : ∀ k, Function.Injective (f k)) (h : Integral v (∏ k, col k)) :
    Integral v (∏ k, rename (f k) (col k)) := by
  rw [integral_iff] at h ⊢
  rw [vG_prod] at h ⊢
  simpa only [vG_rename _ (hf _)] using h
end Formalism.MainNotions.PlaneGram
