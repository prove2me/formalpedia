-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_original_intrinsic_signed_occupation_fubini_ae_fibres
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:08:12.807207+00:00
-- url     : https://prove2.me/submissions/35e13b84-2b48-4840-bc4d-cb19bac9db51

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
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω = ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hHi : Integrable H M)
    (hPosHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] (fun p => ENNReal.ofReal (H p)))
    (hNegHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] (fun p => ENNReal.ofReal (-H p)))
    (hFibre : ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω))
    (hPosFin : ∀ᵐ ω ∂P, (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)) < ∞)
    (hNegFin : ∀ᵐ ω ∂P, (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)) < ∞)
    (hPosI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P)
    (hNegI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P) :
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
  have hpos := AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
      X NX hNX K hK hKmeas
      (fun ω => avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω)
      M hM (fun p => ENNReal.ofReal (H p)) hPosHm
  have hneg := AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
      X NX hNX K hK hKmeas
      (fun ω => avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω)
      M hM (fun p => ENNReal.ofReal (-H p)) hNegHm
  have hinner : ∀ᵐ ω ∂P,
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) =
        (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal -
        (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal := by
    filter_upwards [hFibre] with ω hω
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω
  calc
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) =
        ∫ ω, (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal -
          (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal ∂P := by
      exact integral_congr_ae hinner
    _ = (∫ ω, (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal ∂P) -
        (∫ ω, (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal ∂P) :=
      integral_sub hPosI hNegI
    _ = (∫⁻ ω, ∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω) ∂P).toReal -
        (∫⁻ ω, ∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω) ∂P).toReal := by
      rw [integral_toReal hPosAem hPosFin, integral_toReal hNegAem hNegFin]
    _ = (∫⁻ p, ENNReal.ofReal (H p) ∂M).toReal -
        (∫⁻ p, ENNReal.ofReal (-H p) ∂M).toReal := by
      rw [hpos, hneg]
    _ = ∫ p, H p ∂M :=
      (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi).symm