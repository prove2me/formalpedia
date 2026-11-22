-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_N_null
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:03.804824+00:00
-- url     : https://prove2.me/submissions/558c0b3f-fa00-48e7-99fc-e8ce12c7b124

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
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
private theorem rr_N_eq_iUnion_preimage_inter :
    rr_N Γ D = ⋃ a : Γ, ⋃ b : Γ, ⋃ (_ : a ≠ b),
      ((fun y => (a : G) * y) ⁻¹' D ∩ (fun y => (b : G) * y) ⁻¹' D) := by
  ext y
  simp only [mem_rr_N_iff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨a, ha, b, hb, hab, h1, h2⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun e => hab (congrArg Subtype.val e), h1, h2⟩
  · rintro ⟨a, b, hab, h1, h2⟩
    exact ⟨a, a.2, b, b.2, fun e => hab (Subtype.ext e), h1, h2⟩
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
theorem _root_.solution [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) : μ (rr_N Γ D) = 0 := by
  rw [rr_N_eq_iUnion_preimage_inter]
  refine measure_iUnion_null fun a => measure_iUnion_null fun b => measure_iUnion_null fun hab => ?_
  have hne : (a : G) * (b : G)⁻¹ ≠ 1 := fun e => hab (Subtype.ext (mul_inv_eq_one.mp e))
  have hmem : (a : G) * (b : G)⁻¹ ∈ (Γ : Set G) := Γ.mul_mem a.2 (Γ.inv_mem b.2)
  have hsub : (fun y => (a : G) * y) ⁻¹' D ∩ (fun y => (b : G) * y) ⁻¹' D ⊆
      (fun y => (a : G) * y) ⁻¹' ((fun z => (a : G) * (b : G)⁻¹ * z) '' D ∩ D) := by
    rintro y ⟨h1, h2⟩
    refine ⟨⟨(b : G) * y, h2, ?_⟩, h1⟩
    simp only [mul_assoc, inv_mul_cancel_left]
  refine measure_mono_null hsub ?_
  rw [measure_preimage_mul]
  exact h.disj _ hmem hne
end Formalism.MainNotions.LeviCoordinates
