-- Prove2me | solution 1 for Formalism.REAL.re_inner_self_indexArray
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:14.73686+00:00
-- url     : https://prove2.me/submissions/9a67eacc-6a9c-4727-bcff-491b0a7208d4

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero

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
theorem _root_.solution (F : Arr V n j) : (⟪F, F⟫_ℂ).re = ‖F‖ ^ 2 := by
  first
    | exact inner_self_eq_norm_sq F
    | exact inner_self_eq_norm_sq (𝕜 := ℂ) F
    | simpa using inner_self_eq_norm_sq (𝕜 := ℂ) F
end Formalism.REAL
