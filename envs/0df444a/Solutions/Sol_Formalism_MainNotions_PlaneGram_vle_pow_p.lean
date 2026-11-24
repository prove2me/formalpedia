-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vle_pow_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:40:55.38059+00:00
-- url     : https://prove2.me/submissions/2c940acf-d961-4787-ba96-dbcfd6e9ec4f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vle_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vle_p_pow

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
theorem _root_.solution (hD : DVRHyp v p) {a : ℝ} {x : K} (n : ℕ) (hx : vle v a x) :
    vle v (a + n) ((p : K) ^ n * x) := by
  rw [add_comm]
  exact vle_mul v (vle_p_pow hD n) hx
end Formalism.MainNotions.PlaneGram
