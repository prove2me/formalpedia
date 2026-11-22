-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_rep_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:16.908363+00:00
-- url     : https://prove2.me/submissions/a5c9bb4c-3f06-4ed3-9154-66299b0164d4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep

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
theorem _root_.solution (h : rr_FD μ Γ D) (y : G) :
    ∃ γ ∈ Γ, rr_rep (Γ : Set G) D y = γ * y ∧ γ * y ∈ D := by
  have hex : ∃ γ ∈ (Γ : Set G), γ * y ∈ D := h.cov y
  refine ⟨hex.choose, hex.choose_spec.1, ?_, hex.choose_spec.2⟩
  unfold rr_rep
  rw [dif_pos hex]
end Formalism.MainNotions.LeviCoordinates
