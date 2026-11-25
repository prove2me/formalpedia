-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.dg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:19:06.633893+00:00
-- url     : https://prove2.me/submissions/ea10bc2c-99a3-4acd-b940-753ff4e18588

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
theorem _root_.solution {σ : Type} (f g : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg (fun α => f α * g α) F = dg f (dg g F) := by
  ext β; simp only [coeff_dg]; ring
end Formalism.MainNotions.PlaneGram
