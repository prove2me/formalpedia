-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_bin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:30.458682+00:00
-- url     : https://prove2.me/submissions/5d2e920f-9962-4730-accf-ed6a4eb2216d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_natCast


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
variable {σ : Type} [Fintype σ]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (v : AddValuation K (WithTop ℚ)) (M α : σ →₀ ℕ) : vge v 0 (bin M α : K) := by
  have h : (bin M α : K) = ((∏ x, (α x).choose (M x) : ℕ) : K) := by
    rw [bin, Nat.cast_prod]
  rw [h]
  exact vge_natCast v _
end Formalism.MainNotions.PlaneGram
