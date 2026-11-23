-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.exists_coeff_eq_vG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:15.659274+00:00
-- url     : https://prove2.me/submissions/3a439474-e20f-4ea7-b6c0-0d3e82f61bf5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder

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
theorem _root_.solution (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ α ∈ F.support, v (F.coeff α) = vG v F := by
  have hne : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; exact hF (support_eq_empty.mp h)
  obtain ⟨α, hα, h⟩ := Finset.exists_mem_eq_inf F.support hne fun α => v (F.coeff α)
  exact ⟨α, hα, h.symm⟩
end Formalism.MainNotions.PlaneGram
