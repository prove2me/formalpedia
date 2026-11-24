-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vG_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:29.90449+00:00
-- url     : https://prove2.me/submissions/9510ddbb-da0d-4993-b465-2c105f10d373

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_vG_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vG_le_coeff

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
theorem _root_.solution (f : σ → τ) (hf : Function.Injective f) (F : MvPolynomial σ K) :
    vG v (rename f F) = vG v F := by
  classical
  apply le_antisymm
  · rw [le_vG_iff]
    intro α
    rw [← coeff_rename_mapDomain f hf F α]
    exact vG_le_coeff _ _
  · rw [le_vG_iff]
    intro β
    by_cases h : ∃ u : σ →₀ ℕ, u.mapDomain f = β
    · obtain ⟨u, rfl⟩ := h
      rw [coeff_rename_mapDomain f hf]
      exact vG_le_coeff _ _
    · rw [coeff_rename_eq_zero f F β (fun u hu => absurd ⟨u, hu⟩ h), AddValuation.map_zero]
      exact le_top
end Formalism.MainNotions.PlaneGram
