-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_unit_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:47.141105+00:00
-- url     : https://prove2.me/submissions/744142df-096c-44bf-a375-fe886b4bf04f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_unit_inv
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_unit_pow

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
theorem _root_.solution {x : K} (h : v x = 0) (ε : ℤ) : v (x ^ ε) = 0 := by
  cases ε with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_natCast]
    exact v_unit_pow v h n
  | negSucc n =>
    rw [zpow_negSucc]
    exact v_unit_inv v (v_unit_pow v h _)
end Formalism.MainNotions.PlaneGram
