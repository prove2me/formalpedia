-- Prove2me | solution 1 for Formalism.REAL.re_inner_self_eq_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:00.378281+00:00
-- url     : https://prove2.me/submissions/b44ba4fd-ae8d-41eb-a4b2-b79b0c23806b

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (x : W) :
    (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
  have := @norm_sq_eq_re_inner ℂ _ _ _ _ x
  rw [this]
  simp
end Formalism.REAL
