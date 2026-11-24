-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vN_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:11.923655+00:00
-- url     : https://prove2.me/submissions/e136bc9d-b118-4b6e-8876-2a2daef6fc81

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
theorem _root_.solution (hD : DVRHyp v p) (n : ℕ) : vN v n = padicValNat p n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [vN]
  · unfold vN
    rw [v_natCast hD hn, WithTop.untopD_coe, Rat.cast_natCast]
end Formalism.MainNotions.PlaneGram
