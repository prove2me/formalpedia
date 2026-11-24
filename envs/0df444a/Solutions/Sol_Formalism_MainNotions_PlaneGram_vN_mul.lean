-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vN_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:08:16.790113+00:00
-- url     : https://prove2.me/submissions/d7fa36b8-4a15-451e-8170-b4166b85af34

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_eq

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
theorem _root_.solution (hD : DVRHyp v p) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    vN v (m * n) = vN v m + vN v n := by
  haveI := Fact.mk hD.prime
  rw [vN_eq hD, vN_eq hD, vN_eq hD, padicValNat.mul hm hn]
  push_cast
  ring
end Formalism.MainNotions.PlaneGram
