-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_sub_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:33.913282+00:00
-- url     : https://prove2.me/submissions/b41915b3-8b31-4e20-a725-497471798b0d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight

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
variable (v : AddValuation K (WithTop ℚ)) {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (a w : ℝ) (x : K) :
    vge v (a - w) x ↔ ((a : ℝ) : WithTop ℝ) ≤ vR v x + ((w : ℝ) : WithTop ℝ) := by
  unfold vge
  cases vR v x with
  | top => simp
  | coe y =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]
end Formalism.MainNotions.PlaneGram
