-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vle_vN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:54:12.757543+00:00
-- url     : https://prove2.me/submissions/3af16239-e23b-4e41-8f27-b62d558b5610

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_natCast

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
theorem _root_.solution (hD : DVRHyp v p) {n : ℕ} (hn : n ≠ 0) : vle v (vN v n) (n : K) := by
  unfold vle vR vN
  rw [v_natCast hD hn, WithTop.untopD_coe, WithTop.map_coe]
end Formalism.MainNotions.PlaneGram
