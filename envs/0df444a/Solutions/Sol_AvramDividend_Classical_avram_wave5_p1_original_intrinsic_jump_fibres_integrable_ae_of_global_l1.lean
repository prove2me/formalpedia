-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_fibres_integrable_ae_of_global_l1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:44:59.074219+00:00
-- url     : https://prove2.me/submissions/7bdd3985-2741-4c95-9eb8-eb8b6ab597ec

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

/-- An integrable actual-source predictable reward has integrable intrinsic jump fibres almost surely. -/
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
    (hHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H)
    (hHi : Integrable H M) :
    ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω) := by
  have hEnorm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ‖H p‖ₑ) := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      @Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)
    exact hHm.enorm
  have hBind :=
    avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
      X NX hNX K hK hKmeas
      (fun ω => avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω)
      M hM (fun p => ‖H p‖ₑ) hEnorm
  have hNorm : (∫⁻ p, ‖H p‖ₑ ∂M) < ∞ := hHi.hasFiniteIntegral
  have hOuter : (∫⁻ ω, ∫⁻ p, ‖H ((p.1, ω), p.2)‖ₑ ∂(NX ω) ∂P) < ∞ := by
    rw [← hBind]
    exact hNorm
  have hOuterAem :
      AEMeasurable (fun ω =>
        ∫⁻ p, ‖H ((p.1, ω), p.2)‖ₑ ∂(NX ω)) P :=
    avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
      X NX hNX K hK hKmeas (fun p => ‖H p‖ₑ) hEnorm
  have hFibreFin : ∀ᵐ ω ∂P,
      (∫⁻ p, ‖H ((p.1, ω), p.2)‖ₑ ∂(NX ω)) < ∞ :=
    ae_lt_top' hOuterAem hOuter.ne
  filter_upwards [hFibreFin] with ω hω
  have hFibreMeas : Measurable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      @Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)
    exact hHm.comp
      (avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω)
  exact ⟨hFibreMeas.aestronglyMeasurable, hω⟩
