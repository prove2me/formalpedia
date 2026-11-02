-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_integral_integrable_from_global_l1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:56:54.085216+00:00
-- url     : https://prove2.me/submissions/e7f16880-f449-4ccf-88e9-e71599f09eec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original Lévy jump integral is integrable under source occupation L¹ energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hHi : Integrable H M)
    (hHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H)
    (hFibre : ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω)) :
    Integrable (fun ω =>
      ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) P := by
  have hPosHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (H p)) := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      @Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)
    exact ENNReal.measurable_ofReal.comp hHm
  have hNegHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (-H p)) := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      @Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)
    exact ENNReal.measurable_ofReal.comp hHm.neg
  have hPosAem : AEMeasurable (fun ω =>
      ∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)) P :=
    avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
      X NX hNX K hK hKmeas (fun p => ENNReal.ofReal (H p)) hPosHm
  have hNegAem : AEMeasurable (fun ω =>
      ∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)) P :=
    avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
      X NX hNX K hK hKmeas (fun p => ENNReal.ofReal (-H p)) hNegHm
  have hpos :=
    avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
      X NX hNX K hK hKmeas
      (fun ω => avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω)
      M hM (fun p => ENNReal.ofReal (H p)) hPosHm
  have hneg :=
    avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
      X NX hNX K hK hKmeas
      (fun ω => avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω)
      M hM (fun p => ENNReal.ofReal (-H p)) hNegHm
  have hnorm : (∫⁻ p, ‖H p‖ₑ ∂M) < ∞ := hHi.hasFiniteIntegral
  have hPosMass : (∫⁻ p, ENNReal.ofReal (H p) ∂M) < ∞ :=
    lt_of_le_of_lt (lintegral_mono (fun p => Real.ofReal_le_enorm (H p))) hnorm
  have hNegMass : (∫⁻ p, ENNReal.ofReal (-H p) ∂M) < ∞ :=
    lt_of_le_of_lt (lintegral_mono (fun p => by
      simpa only [enorm_neg] using Real.ofReal_le_enorm (-H p))) hnorm
  have hPosTotal :
      (∫⁻ ω, ∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω) ∂P) < ∞ := by
    rw [← hpos]
    exact hPosMass
  have hNegTotal :
      (∫⁻ ω, ∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω) ∂P) < ∞ := by
    rw [← hneg]
    exact hNegMass
  have hPosI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hPosAem hPosTotal.ne
  have hNegI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hNegAem hNegTotal.ne
  have hinner : (fun ω =>
      ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) =ᵐ[P]
      (fun ω =>
        (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal -
        (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal) := by
    filter_upwards [hFibre] with ω hω
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω
  exact (integrable_congr hinner).2 (hPosI.sub hNegI)