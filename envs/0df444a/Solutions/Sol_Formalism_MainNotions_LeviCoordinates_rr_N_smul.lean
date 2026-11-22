-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_N_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:24.982025+00:00
-- url     : https://prove2.me/submissions/ab10c84d-1c48-49c5-955f-18ef2129e1f6

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
theorem _root_.solution {y c : G} (hc : c ∈ Γ) (hy : y ∉ rr_N Γ D) : c * y ∉ rr_N Γ D := by
  intro hcy
  obtain ⟨g1, hg1, g2, hg2, hne, h1, h2⟩ := mem_rr_N_iff.mp hcy
  refine hy (mem_rr_N_iff.mpr ⟨g1 * c, Γ.mul_mem hg1 hc, g2 * c, Γ.mul_mem hg2 hc,
    fun e => hne (mul_right_cancel e), ?_, ?_⟩)
  · rwa [mul_assoc]
  · rwa [mul_assoc]
end Formalism.MainNotions.LeviCoordinates
