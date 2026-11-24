-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.shift_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:27.187795+00:00
-- url     : https://prove2.me/submissions/a51bb1f8-c984-4dda-87f7-0259c3a6ec35

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_measure_SF_eq
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_SF_mul_right
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_int_eq
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_SF_measure_univ
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_SF_measure_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (R Γ : Subgroup G) [Countable Γ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : G → E) (Ω : Set G) (h : G) (ν : Measure G)
    (hΓR : Γ ≤ R) (hK : ∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K)
    (hn : ∀ r, r ∈ R ↔ h⁻¹ * r * h ∈ R) (hσ : SigmaFinite ν) (hne : ν ≠ 0) (hcon : ν (R : Set G)ᶜ = 0)
    (hfin : ∀ K : Set G, IsCompact K → ν K < ⊤) (hleft : ∀ r ∈ R, ν.map (fun x => r * x) = ν)
    (hinvν : ν.map (fun x => x⁻¹) = ν) (hconj : ν.map (fun x => h⁻¹ * x * h) = ν)
    (hf : ∀ r ∈ R, ∀ x, f (r * x) = f x) (hΩ : SF (Γ : Set G) Ω) (hfi : IntegrableOn f Ω μ) :
    ∫ x in Ω, f x ∂μ = ∫ x in (fun x => h⁻¹ * x) '' Ω, f x ∂μ := by
  have hνΓ : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν := fun s hs => hleft s (hΓR hs)
  obtain ⟨K, hKc, hKR⟩ := hK
  have hlt : ν Ω < ⊤ := by
    have h1 : ν Ω ≤ ν (Ω ∩ (R : Set G)) + ν (R : Set G)ᶜ := by
      calc ν Ω ≤ ν ((Ω ∩ (R : Set G)) ∪ (R : Set G)ᶜ) := by
            refine measure_mono fun x hx => ?_
            by_cases hxR : x ∈ (R : Set G)
            · exact Or.inl ⟨hx, hxR⟩
            · exact Or.inr hxR
        _ ≤ ν (Ω ∩ (R : Set G)) + ν (R : Set G)ᶜ := measure_union_le _ _
    have h2 : ν (Ω ∩ (R : Set G)) ≤ ν K :=
      SF_measure_cover Γ ν hνΓ hΩ (fun x hx => hKR x hx)
    calc ν Ω ≤ ν (Ω ∩ (R : Set G)) + ν (R : Set G)ᶜ := h1
      _ ≤ ν K + ν (R : Set G)ᶜ := by gcongr
      _ = ν K := by rw [hcon, add_zero]
      _ < ⊤ := hfin K hKc
  have hne0 : ν Ω ≠ 0 := by
    intro h0
    apply hne
    have hu := SF_measure_univ Γ ν hνΓ hΩ
    first
    | (rw [h0, tsum_zero] at hu; exact Measure.measure_univ_eq_zero.1 hu)
    | simpa [h0] using hu
  have hcB : ∀ x, ν {r | r * x ∈ {y | h * y ∈ Ω}} = ν Ω := by
    intro x
    have hm : Measurable fun y : G => h⁻¹ * y * h := (measurable_const_mul h⁻¹).mul_const h
    have hS : MeasurableSet {r | r * x ∈ {y | h * y ∈ Ω}} :=
      hΩ.1.preimage ((measurable_mul_const x).const_mul h)
    calc ν {r | r * x ∈ {y | h * y ∈ Ω}}
        = (ν.map (fun x => h⁻¹ * x * h)) {r | r * x ∈ {y | h * y ∈ Ω}} := by rw [hconj]
      _ = ν ((fun y : G => h⁻¹ * y * h) ⁻¹' {r | r * x ∈ {y | h * y ∈ Ω}}) := Measure.map_apply hm hS
      _ = ν {r | r * (h * x) ∈ Ω} := by
          congr 1
          ext r
          simp [mul_assoc]
      _ = ν Ω := measure_SF_eq Γ ν hνΓ (SF_mul_right hΩ (h * x)) hΩ
  have hcA : ∀ y, ν {r | r⁻¹ * y ∈ Ω} = ν Ω := by
    intro y
    have hS : MeasurableSet {r | r⁻¹ * y ∈ Ω} := hΩ.1.preimage (measurable_inv.mul_const y)
    calc ν {r | r⁻¹ * y ∈ Ω} = (ν.map (fun x => x⁻¹)) {r | r⁻¹ * y ∈ Ω} := by rw [hinvν]
      _ = ν ((fun x : G => x⁻¹) ⁻¹' {r | r⁻¹ * y ∈ Ω}) := Measure.map_apply measurable_inv hS
      _ = ν {r | r * y ∈ Ω} := by
          congr 1
          ext r
          simp
      _ = ν Ω := measure_SF_eq Γ ν hνΓ (SF_mul_right hΩ y) hΩ
  have hinvf : ∀ᵐ r ∂ν, ∀ x, f (r⁻¹ * x) = f x := by
    have hR : ∀ᵐ r ∂ν, r ∈ (R : Set G) := ae_iff.2 (by first | exact hcon | simpa using hcon)
    filter_upwards [hR] with r hr x
    exact hf r⁻¹ (R.inv_mem hr) x
  have hfm : AEStronglyMeasurable f μ := by
    have hcov : (⋃ g : Γ, (fun x => (g : G) * x) ⁻¹' Ω) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨s, hs, hsx⟩ := hΩ.2.1 x
      exact Set.mem_iUnion.2 ⟨⟨s, hs⟩, hsx⟩
    have H : AEStronglyMeasurable f (μ.restrict (⋃ g : Γ, (fun x => (g : G) * x) ⁻¹' Ω)) := by
      refine aestronglyMeasurable_iUnion_iff.2 fun g => ?_
      have hmp := (measurePreserving_mul_left μ (g : G)).restrict_preimage hΩ.1
      have k1 : AEStronglyMeasurable (fun x => f ((g : G) * x))
          (μ.restrict ((fun x => (g : G) * x) ⁻¹' Ω)) :=
        hfi.aestronglyMeasurable.comp_measurePreserving hmp
      exact k1.congr (ae_of_all _ fun x => hf (g : G) (hΓR g.2) x)
    rwa [hcov, Measure.restrict_univ] at H
  have hBset : (fun x => h⁻¹ * x) '' Ω = {x | h * x ∈ Ω} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show h * (h⁻¹ * y) ∈ Ω
      simpa using hy
    · intro hx
      exact ⟨h * x, hx, by simp⟩
  rw [hBset]
  exact int_eq ν hΩ.1 (hΩ.1.preimage (measurable_const_mul h)) (ν Ω) hne0
    hlt.ne hcB hcA f hfm hinvf hfi
end Formalism.L2.SG.MeasureShiftInvariance
