-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrkb_step2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:51.444294+00:00
-- url     : https://prove2.me/submissions/d1043f00-c5ba-4158-8d33-4dd9a8a87345

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkbLeOneAddSq
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_mul_le
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_sq_fin
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_r_fix
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
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ) {r : G → G} (hrm : Measurable r)
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (f : Lp ℂ 2 (μ.restrict D)) (x : G)
    (hx : ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) :
    ∫ g, φ g * (f : G → ℂ) (r (x * g)) ∂μ = ∫ y in D, rrk_K Γ φ x y * (f : G → ℂ) y ∂μ := by
  set f0 : G → ℂ := (f : G → ℂ) with hf0
  have hf0m : StronglyMeasurable f0 := Lp.stronglyMeasurable f
  set ψ : G → ℂ := fun y => φ (x⁻¹ * y) * f0 (r y) with hψ
  have hψm : StronglyMeasurable ψ :=
    ((hφm.comp (measurable_const_mul _)).stronglyMeasurable).mul (hf0m.comp_measurable hrm)
  have e1 : ∫ g, φ g * f0 (r (x * g)) ∂μ = ∫ y, ψ y ∂μ := by
    rw [← integral_mul_left_eq_self ψ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [hψ]
  have hfd := rr_isFD h
  have hfix := rrkb_r_fix h hr
  have hγm : ∀ γ : Γ, StronglyMeasurable fun y => ψ (γ • y) := fun γ =>
    hψm.comp_measurable (measurable_const_smul γ)
  have hsum : ∑' γ : Γ, ∫⁻ y in D, ‖ψ (γ • y)‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_tsum (fun γ => (hγm γ).enorm.aemeasurable)]
    have e2 : ∫⁻ y in D, ∑' γ : Γ, ‖ψ (γ • y)‖ₑ ∂μ = ∫⁻ y in D, rrk_Kab Γ φ x y * ‖f0 y‖ₑ ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hfix] with y hy
      rw [rrk_Kab, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      simp only [hψ, Subgroup.smul_def, smul_eq_mul, enorm_mul, hy γ, mul_assoc]
    rw [e2]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun y => rrkb_mul_le _ _)
    rw [lintegral_add_right _ (hf0m.enorm.pow_const 2)]
    exact ENNReal.add_ne_top.2 ⟨hx, rrkb_sq_fin f⟩
  have hψi : Integrable ψ μ := ⟨hψm.aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_enorm, hfd.lintegral_eq_tsum'']
    exact lt_top_iff_ne_top.2 hsum⟩
  rw [e1, hfd.integral_eq_tsum'' ψ hψi, ← integral_tsum (fun γ => (hγm γ).aestronglyMeasurable) hsum]
  refine integral_congr_ae ?_
  filter_upwards [hfix] with y hy
  rw [rrk_K, ← tsum_mul_right]
  refine tsum_congr fun γ => ?_
  simp only [hψ, Subgroup.smul_def, smul_eq_mul, hy γ, mul_assoc]
end Formalism.MainNotions.LeviCoordinates
