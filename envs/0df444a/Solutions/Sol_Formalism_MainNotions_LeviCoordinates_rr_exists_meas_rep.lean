-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_exists_meas_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:01.122713+00:00
-- url     : https://prove2.me/submissions/ddb8a13f-aae9-4417-b538-03041fee8922

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
theorem _root_.solution [Countable Γ] (h : rr_FD μ Γ D) :
    ∃ r : G → G, Measurable r ∧ ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D := by
  classical
  haveI : Nonempty Γ := ⟨1⟩
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  have hex : ∀ y : G, ∃ n : ℕ, ((e n : Γ) : G) * y ∈ D := by
    intro y
    obtain ⟨γ, hγ, hD⟩ := h.cov y
    obtain ⟨n, hn⟩ := he ⟨γ, hγ⟩
    exact ⟨n, by rw [hn]; exact hD⟩
  refine ⟨fun y => ((e (Nat.find (hex y)) : Γ) : G) * y, ?_,
    fun y => ⟨_, (e (Nat.find (hex y))).2, rfl, Nat.find_spec (hex y)⟩⟩
  exact Measurable.find (f := fun n y => ((e n : Γ) : G) * y) (p := fun n y => ((e n : Γ) : G) * y ∈ D)
    (fun n => measurable_const_mul _) (fun n => measurable_const_mul _ h.meas) hex
end Formalism.MainNotions.LeviCoordinates
