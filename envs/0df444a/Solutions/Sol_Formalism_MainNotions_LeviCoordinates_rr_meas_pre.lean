-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_meas_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:48.805927+00:00
-- url     : https://prove2.me/submissions/e4e1b78a-85a9-43eb-a1b5-f0dcca17825f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_N_null
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_eq
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_N_smul
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_smul
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_exists_meas_rep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_FD_right
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_isFD
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
private theorem measurableSet_rr_N [Countable Γ] (hD : MeasurableSet D) :
    MeasurableSet (rr_N Γ D) := by
  rw [rr_N_eq_iUnion_preimage_inter]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ =>
    (measurable_const_mul (a : G) hD).inter (measurable_const_mul (b : G) hD)
end Abs
section Abs2
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
private theorem eq_rr_rep_of_not_mem_rr_N (h : rr_FD μ Γ D) {r : G → G}
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) {y : G} (hy : y ∉ rr_N Γ D) :
    r y = rr_rep (Γ : Set G) D y := by
  obtain ⟨γ, hγ, hry, hD⟩ := hr y
  rw [hry, rr_rep_eq h hy hγ hD]
private theorem rr_rep_eq_self_of_mem_of_not_mem_rr_N (h : rr_FD μ Γ D) {y : G}
    (hy : y ∉ rr_N Γ D) (hD : y ∈ D) : rr_rep (Γ : Set G) D y = y := by
  have e := rr_rep_eq h hy Γ.one_mem (by rwa [one_mul])
  rwa [one_mul] at e
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
theorem _root_.solution [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) {r : G → G}
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G) {A : Set G} (hA : MeasurableSet A) :
    μ ((fun x => r (x * g)) ⁻¹' A ∩ D) = μ (A ∩ D) := by
  obtain ⟨r₀, hr₀, hr₀rep⟩ := rr_exists_meas_rep h
  haveI : MeasurableConstSMul Γ G := ⟨fun c => measurable_const_mul (c : G)⟩
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun c s _ => measure_preimage_mul μ (c : G) s⟩
  have hMmeas : MeasurableSet (rr_N Γ D) := measurableSet_rr_N h.meas
  have hN0 : μ ((fun x => x * g) ⁻¹' rr_N Γ D) = 0 := by
    rw [measure_preimage_mul_right]; exact rr_N_null h
  have hN : ∀ᵐ x ∂μ, x * g ∉ rr_N Γ D := by
    refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) hN0)
    simp only [Set.mem_setOf_eq, not_not] at hx
    exact hx
  have hSmeas : MeasurableSet ((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) :=
    measurable_mul_const g (hMmeas.compl.inter (hr₀ hA))
  have hinv : ∀ c : Γ, (fun x => c • x) ⁻¹' ((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) = ((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) := by
    intro c
    ext x
    show (c : G) * x * g ∉ rr_N Γ D ∧ r₀ ((c : G) * x * g) ∈ A ↔
      x * g ∉ rr_N Γ D ∧ r₀ (x * g) ∈ A
    rw [mul_assoc]
    constructor
    · rintro ⟨h1, h2⟩
      have hy : x * g ∉ rr_N Γ D := by
        have e := rr_N_smul (Γ.inv_mem c.2) h1
        rwa [inv_mul_cancel_left] at e
      refine ⟨hy, ?_⟩
      rwa [eq_rr_rep_of_not_mem_rr_N h hr₀rep h1, rr_rep_smul h c.2 hy,
        ← eq_rr_rep_of_not_mem_rr_N h hr₀rep hy] at h2
    · rintro ⟨h1, h2⟩
      have hy := rr_N_smul c.2 h1
      refine ⟨hy, ?_⟩
      rwa [eq_rr_rep_of_not_mem_rr_N h hr₀rep hy, rr_rep_smul h c.2 h1, ← eq_rr_rep_of_not_mem_rr_N h hr₀rep h1]
  have hfd : IsFundamentalDomain Γ D μ := (rr_isFD h)
  have hfd' : IsFundamentalDomain Γ ((fun x => x * g) ⁻¹' D) μ :=
    (rr_isFD ((rr_FD_right h) g))
  have key := hfd.measure_set_eq hfd' (A := ((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A))) hSmeas hinv
  have e1 : μ ((fun x => r (x * g)) ⁻¹' A ∩ D) = μ (((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) ∩ D) := by
    refine measure_congr (hN.mono fun x hx => propext ?_)
    have e : r (x * g) = r₀ (x * g) := by
      rw [eq_rr_rep_of_not_mem_rr_N h hr hx, eq_rr_rep_of_not_mem_rr_N h hr₀rep hx]
    show r (x * g) ∈ A ∧ x ∈ D ↔ (x * g ∉ rr_N Γ D ∧ r₀ (x * g) ∈ A) ∧ x ∈ D
    rw [e]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hx, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩⟩
  have e2 : μ (((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) ∩ (fun x => x * g) ⁻¹' D) = μ ((fun x => x * g) ⁻¹' (A ∩ D)) := by
    refine measure_congr (hN.mono fun x hx => propext ?_)
    show (x * g ∉ rr_N Γ D ∧ r₀ (x * g) ∈ A) ∧ x * g ∈ D ↔ x * g ∈ A ∧ x * g ∈ D
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩
      refine ⟨?_, h2⟩
      rwa [eq_rr_rep_of_not_mem_rr_N h hr₀rep hx, rr_rep_eq_self_of_mem_of_not_mem_rr_N h hx h2] at h1
    · rintro ⟨h1, h2⟩
      refine ⟨⟨hx, ?_⟩, h2⟩
      rwa [eq_rr_rep_of_not_mem_rr_N h hr₀rep hx, rr_rep_eq_self_of_mem_of_not_mem_rr_N h hx h2]
  rw [e1, key, e2, measure_preimage_mul_right]
end Formalism.MainNotions.LeviCoordinates
