-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrkb_lint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:24.776388+00:00
-- url     : https://prove2.me/submissions/051fe77b-510d-487f-bbf0-aacabc35fd5f

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkbLeOneAddSq
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_map
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_ae_eq


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
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (h : rr_FD μ Γ D) {r : G → G} (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G)
    {F : G → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x in D, F (r (x * g)) ∂μ = ∫⁻ x in D, F x ∂μ := by
  obtain ⟨h1, h2⟩ := rr_map h g
  calc ∫⁻ x in D, F (r (x * g)) ∂μ = ∫⁻ x in D, F (rr_rep (Γ : Set G) D (x * g)) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr g)] with x hx
        rw [hx]
    _ = ∫⁻ y, F y ∂(Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)) :=
        (lintegral_map' hF.aemeasurable h1).symm
    _ = ∫⁻ x in D, F x ∂μ := by rw [h2]
end Formalism.MainNotions.LeviCoordinates
