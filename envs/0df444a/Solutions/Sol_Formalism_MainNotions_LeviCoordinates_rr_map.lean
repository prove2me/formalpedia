-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:21.324445+00:00
-- url     : https://prove2.me/submissions/5aad8baf-61eb-43a3-acf9-3c43f9001b09

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_spec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_exists_meas_rep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_ae_eq
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_meas_pre

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
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) (g : G) :
    AEMeasurable (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) ∧
      Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) = μ.restrict D := by
  obtain ⟨r₀, hr₀, hr₀rep⟩ := rr_exists_meas_rep h
  have hae : AEMeasurable (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) :=
    ⟨fun x => r₀ (x * g), hr₀.comp (measurable_mul_const g),
      ae_restrict_of_ae (rr_rep_ae_eq h hr₀rep g)⟩
  refine ⟨hae, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply_of_aemeasurable hae hA, Measure.restrict_apply' h.meas,
    Measure.restrict_apply' h.meas]
  exact rr_meas_pre h (rr_rep_spec h) g hA
end Formalism.MainNotions.LeviCoordinates
