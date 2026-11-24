-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_natCast_nonneg_monomial_order_segments
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:35.41901+00:00
-- url     : https://prove2.me/submissions/8faf64f8-4858-4c03-9545-600b554b56fb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => rw [Nat.cast_zero, AddValuation.map_zero]; exact le_top
  | succ k ih =>
    rw [Nat.cast_succ]
    exact le_trans (le_min ih (le_of_eq (AddValuation.map_one v).symm)) (AddValuation.map_add v _ _)
end Formalism.MainNotions.PlaneGram
