-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:11:43.521135+00:00
-- url     : https://prove2.me/submissions/64972121-fd20-4744-b561-8a405b6b2e1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

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
        (fun u : ℝ≥0 =>
          (u, X.X u ω -
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
    (hLift : ∀ ω,
      @Measurable (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p => ((p.1, ω), p.2)))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ≥0∞)
    (hHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H) :
    (∫⁻ p, H p ∂M) =
      ∫⁻ ω, ∫⁻ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P := by
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
      hHm (hLift ω)
  rw [hM, Measure.lintegral_bind hKmeas hHm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [] with ω
  exact hMap ω
