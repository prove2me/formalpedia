-- Prove2me | solution 1 for Formalism.HN.Rerealization.eq_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:17.904538+00:00
-- url     : https://prove2.me/submissions/44c66c50-5e0f-47f3-966b-2917fd288eb6

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.Rerealization
variable {G E F : Type*} [AddCommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
namespace Formalism.HN.Rerealization
theorem _root_.solution (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) {x y : G}
    (h : α x = α y) : β x = β y := by
  have h0 : ‖β (x - y)‖ = 0 := by rw [hn, map_sub, h, sub_self, norm_zero]
  rw [norm_eq_zero, map_sub, sub_eq_zero] at h0
  exact h0
end Formalism.HN.Rerealization
