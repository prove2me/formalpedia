-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vG_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:27.386106+00:00
-- url     : https://prove2.me/submissions/aa0f9670-cc5a-4dae-80d4-b16e5d4c620f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Theorems.Thm_Formalism_MainNotions_PlaneGram_exists_coeff_eq_vG

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
theorem _root_.solution (F : MvPolynomial σ K) (hF : F ≠ 0) : vG v F ≠ ⊤ := by
  obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) F hF
  rw [← h]
  intro ht
  exact (mem_support_iff.mp hα) ((AddValuation.top_iff v).mp ht)
end Formalism.MainNotions.PlaneGram
