-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrka_summable_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:41.592668+00:00
-- url     : https://prove2.me/submissions/ea2cd3ca-fa6b-4b13-9510-6fd801c4db0f

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkaMeasKabRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution {ι : Type*} {f : ι → ℂ} (hf : ∑' i, ‖f i‖ₑ ≠ ∞) : Summable f :=
  Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 hf)
end Formalism.MainNotions.LeviCoordinates
