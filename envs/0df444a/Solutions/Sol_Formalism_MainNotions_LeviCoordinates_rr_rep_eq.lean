-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_rep_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:19.429542+00:00
-- url     : https://prove2.me/submissions/7961e5ed-62ed-4a07-aa9f-daaca5595832

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal Pointwise InnerProductSpace
section Abs
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
private theorem mem_rr_N_iff {y : G} :
    y ∈ rr_N Γ D ↔ ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * y ∈ D ∧ γ₂ * y ∈ D := Iff.rfl
end Abs
section Abs2
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
end Abs2
end Formalism.MainNotions.LeviCoordinates
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (h : rr_FD μ Γ D) {y : G} (hy : y ∉ rr_N Γ D) {γ : G} (hγ : γ ∈ Γ) (hD : γ * y ∈ D) :
    rr_rep (Γ : Set G) D y = γ * y := by
  obtain ⟨γ₀, hγ₀, he, hD₀⟩ := rr_rep_spec h y
  rw [he]
  by_contra hne
  exact hy (mem_rr_N_iff.mpr ⟨γ₀, hγ₀, γ, hγ, fun e => hne (by rw [e]), hD₀, hD⟩)
end Formalism.MainNotions.LeviCoordinates
