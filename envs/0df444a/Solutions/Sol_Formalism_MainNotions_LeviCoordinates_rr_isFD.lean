-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_isFD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:11.19337+00:00
-- url     : https://prove2.me/submissions/109a2fe8-bbe1-4ac5-ac0b-adf931254f36

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
theorem _root_.solution [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) : IsFundamentalDomain Γ D μ := by
  refine IsFundamentalDomain.mk'' h.meas.nullMeasurableSet
    (ae_of_all _ fun y => ?_) (fun g hg => ?_) (fun g => ?_)
  · obtain ⟨γ, hγ, hD⟩ := h.cov y
    exact ⟨⟨γ, hγ⟩, hD⟩
  · exact h.disj g g.2 (fun e => hg (Subtype.ext e))
  · exact (measurePreserving_mul_left μ (g : G)).quasiMeasurePreserving
end Formalism.MainNotions.LeviCoordinates
