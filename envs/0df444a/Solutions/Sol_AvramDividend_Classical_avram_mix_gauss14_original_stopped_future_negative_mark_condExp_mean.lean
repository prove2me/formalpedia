-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_stopped_future_negative_mark_condExp_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:50:34.484764+00:00
-- url     : https://prove2.me/submissions/d49149e3-a361-4951-9a76-a2601686be32

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_stopped_future_signed_negative_mark_independent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Conditional centring of the original future signed jump mass at a genuine stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : ∀ z ∈ B, z ≤ 0)
    (J : Ω → Measure (ℝ≥0 × ℝ))
    (hJ : J = fun ω =>
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (F : Ω → ℝ)
    (hF : F = fun ω =>
      ∫ p in (Ioc (τ ω) (τ ω + T) ×ˢ B), p.2 ∂J ω)
    (hStrong : StronglyMeasurable F)
    (hInt : Integrable F P)
    (hPast : (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace ≤ mΩ) :
    P[F | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P]
      (fun _ => ∫ ω, F ω ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hInd : Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap F inferInstance) P := by
    subst F
    subst J
    exact avram_mix_gauss14_original_stopped_future_signed_negative_mark_independent
      X τ hτ T B hB hNeg
  have hMeas : Measurable F := hStrong.measurable
  have hC : StronglyMeasurable[MeasurableSpace.comap F inferInstance] F :=
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  exact condExp_indep_eq hMeas.comap_le hPast hC hInd.symm
