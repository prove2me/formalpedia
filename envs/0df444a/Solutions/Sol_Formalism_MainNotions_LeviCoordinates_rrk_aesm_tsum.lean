-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrk_aesm_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:37.409653+00:00
-- url     : https://prove2.me/submissions/c89efff6-1944-4001-aeb7-14505286eac5

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum

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
variable {G : Type*} [Group G]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hs : ∀ᵐ x ∂μ, Summable fun i => f i x) :
    AEStronglyMeasurable (fun x => ∑' i, f i x) μ := by
  refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
    (f := fun s x => ∑ i ∈ s, f i x) (fun s => ?_) ?_
  · exact Finset.aestronglyMeasurable_fun_sum s fun i _ => hf i
  · filter_upwards [hs] with x hx
    exact hx.hasSum
end Formalism.MainNotions.LeviCoordinates
