-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_intCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:33.544329+00:00
-- url     : https://prove2.me/submissions/b39ce8e1-2e56-40bc-965c-2303ada5d237

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_natCast_nonneg

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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (z : ℤ) : 0 ≤ v (z : K) := by
  cases z with
  | ofNat n => simpa using v_natCast_nonneg v n
  | negSucc n =>
    rw [Int.cast_negSucc, AddValuation.map_neg]
    exact v_natCast_nonneg v (n + 1)
end Formalism.MainNotions.PlaneGram
