-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_original_intrinsic_signed_fubini_from_global_l1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:34:32.023934+00:00
-- url     : https://prove2.me/submissions/d7aec9e3-453c-4515-a29f-aee2a8e91898

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_signed_occupation_fubini_ae_fibres
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual intrinsic source jump reward obeys signed Fubini under global L¹ energy. -/
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
    (hPosHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (H p)))
    (hNegHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (-H p)))
    (hFibre : ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω)) :
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) =
      ∫ p, H p ∂M := by
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
  have hPosFin : ∀ᵐ ω ∂P,
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)) < ∞ :=
    ae_lt_top' hPosAem hPosTotal.ne
  have hNegFin : ∀ᵐ ω ∂P,
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)) < ∞ :=
    ae_lt_top' hNegAem hNegTotal.ne
  have hPosI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hPosAem hPosTotal.ne
  have hNegI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hNegAem hNegTotal.ne
  exact avram_wave5_p1_original_intrinsic_signed_occupation_fubini_ae_fibres
    X NX hNX K hK hKmeas M hM H hHi hPosHm hNegHm
    hFibre hPosFin hNegFin hPosI hNegI
