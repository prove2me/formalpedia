-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_actual_source_signed_fubini_finite_horizon_restriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:15:07.172771+00:00
-- url     : https://prove2.me/submissions/a7250271-e101-4ec8-987b-6fb9203dfccb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_signed_occupation_fubini_ae_fibres
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
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] S)
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hSupport : S.indicator H = H)
    (hHi : Integrable H M)
    (hPosHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (H p)))
    (hNegHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (-H p)))
    (hFibre : ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω))
    (hPosFin : ∀ᵐ ω ∂P,
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)) < ∞)
    (hNegFin : ∀ᵐ ω ∂P,
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)) < ∞)
    (hPosI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P)
    (hNegI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P) :
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) =
      ∫ p, H p ∂MT := by
  have hfubini :=
    AvramDividend.Classical.avram_wave5_p1_original_intrinsic_signed_occupation_fubini_ae_fibres
      X NX hNX K hK hKmeas M hM H hHi hPosHm hNegHm
      hFibre hPosFin hNegFin hPosI hNegI
  calc
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) = ∫ p, H p ∂M := hfubini
    _ = ∫ p, H p ∂MT := by
      rw [hMT, ← integral_indicator hS, hSupport]
