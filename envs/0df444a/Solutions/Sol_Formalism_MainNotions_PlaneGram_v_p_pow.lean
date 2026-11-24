-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_p_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:21.062827+00:00
-- url     : https://prove2.me/submissions/a551c757-0b7f-4aa4-8e8c-34d35ec00a3a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_nsmul_one_withTop

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
variable {v} {p : ℕ} [CharZero K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hD : DVRHyp v p) (n : ℕ) : v ((p : K) ^ n) = ((n : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_pow, hD.vp, nsmul_one_withTop]
end Formalism.MainNotions.PlaneGram
