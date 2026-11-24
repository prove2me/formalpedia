-- Prove2me | solution 1 for Formalism.REAL.norm_sq_eq_sum_firstPositionSlice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:02.896345+00:00
-- url     : https://prove2.me/submissions/83946a91-1fb5-4530-97b4-29450be23792

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_inner_eq_sum_firstPositionSlice
import Theorems.Thm_Formalism_REAL_re_inner_self_indexArray

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (F : Arr V n (j+1)) :
    ‖F‖ ^ 2 = ∑ α' : Fin j → Fin n × Fin n, ‖sliceLin V n α' F‖ ^ 2 := by
  rw [← re_inner_self_indexArray, inner_eq_sum_firstPositionSlice, Complex.re_sum]
  simp only [re_inner_self_indexArray]
end Formalism.REAL
