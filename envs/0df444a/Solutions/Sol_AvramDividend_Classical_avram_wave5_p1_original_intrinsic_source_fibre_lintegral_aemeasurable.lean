-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:01:33.913397+00:00
-- url     : https://prove2.me/submissions/659e0912-22dc-4661-83f6-70a7479f8b62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable

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
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ≥0∞)
    (hHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H) :
    AEMeasurable (fun ω => ∫⁻ p, H ((p.1, ω), p.2) ∂(NX ω)) P := by
  have hMap (ω : Ω) :
      (∫⁻ q, H q ∂(K ω)) =
        ∫⁻ p, H ((p.1, ω), p.2) ∂(NX ω) := by
    rw [hK ω]
    exact @lintegral_map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ))
      (NX ω) H
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
      hHm
      (avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω)
  have hAE : AEMeasurable (fun ω => ∫⁻ q, H q ∂(K ω)) P :=
    (Measure.measurable_lintegral hHm).comp_aemeasurable hKmeas
  have heq :
      (fun ω : Ω => ∫⁻ q, H q ∂(K ω)) =
        (fun ω : Ω => ∫⁻ p, H ((p.1, ω), p.2) ∂(NX ω)) :=
    funext hMap
  rw [← heq]
  exact hAE
