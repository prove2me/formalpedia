-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_right_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:40.144931+00:00
-- url     : https://prove2.me/submissions/0097aef7-ec54-43f6-8141-24ea4764717b

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrRightOfFinite
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_isFD


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
open scoped ENNReal Pointwise
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [SigmaFinite μ] [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) (hfin : μ D ≠ ⊤) :
    μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  by_cases h0 : μ D = 0
  · have hu : μ univ = 0 := by
      have hs : (univ : Set G) ⊆ ⋃ γ : Γ, (fun y => (γ : G) * y) ⁻¹' D := fun y _ => by
        obtain ⟨γ, hγ, hD⟩ := h.cov y
        exact mem_iUnion.2 ⟨⟨γ, hγ⟩, hD⟩
      refine measure_mono_null hs ?_
      rw [measure_iUnion_null_iff]; intro γ
      rw [measure_preimage_mul]; exact h0
    have hz : μ = 0 := Measure.measure_univ_eq_zero.1 hu
    rw [hz]; simp
  · set ν := Measure.map (fun x => x * g) μ with hν
    have i1 : ν.IsMulLeftInvariant := isMulLeftInvariant_map_mul_right g
    have i2 : SigmaFinite ν := (MeasurableEquiv.mulRight g).sigmaFinite_map (μ := μ)
    have e := measure_eq_div_smul ν μ h0 hfin
    have hD' : rr_FD μ Γ ((fun x => x * g) ⁻¹' D) :=
      { meas := (measurable_mul_const g) h.meas
        cov := fun y => by
          obtain ⟨γ, hγ, hD⟩ := h.cov (y * g)
          exact ⟨γ, hγ, by simpa [mul_assoc] using hD⟩
        disj := fun γ hγ h1 => by
          have hs : (fun y => γ * y) '' ((fun x => x * g) ⁻¹' D) ∩ (fun x => x * g) ⁻¹' D ⊆
              (fun x => x * g) ⁻¹' ((fun y => γ * y) '' D ∩ D) := by
            rintro _ ⟨⟨y, hy, rfl⟩, h2⟩
            exact ⟨⟨y * g, hy, by simp [mul_assoc]⟩, h2⟩
          refine measure_mono_null hs ?_
          refine Measure.preimage_null_of_map_null (measurable_mul_const g).aemeasurable ?_
          have e' : ν ((fun y => γ * y) '' D ∩ D) = ((ν D / μ D) • μ) ((fun y => γ * y) '' D ∩ D) := by rw [← e]
          rw [← hν, e', Measure.smul_apply, h.disj γ hγ h1]
          simp }
    have hm : μ ((fun x => x * g) ⁻¹' D) = μ D := (rr_isFD hD').measure_eq (rr_isFD h)
    have hνD : ν D = μ D := by rw [hν, Measure.map_apply (measurable_mul_const g) h.meas, hm]
    rw [e, hνD, ENNReal.div_self h0 hfin, one_smul]
end Formalism.MainNotions.LeviCoordinates
