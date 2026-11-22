-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_actual_stopped_NX_signed_compensator_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:46:06.211177+00:00
-- url     : https://prove2.me/submissions/b50982f7-1745-445e-97b3-e769250020de

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_literal_original_stopped_signed_L1_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_NX_marked_integral_indicator
open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _
          (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    ∀ (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K) (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T})
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S)
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (σ : Ω → ℝ≥0) (hσeq : ∀ ω, τ ω = (σ ω : ℝ≥0∞))
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGiN : Integrable G N)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hSupport : S.indicator H = H),
    let SNX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
      MeasureTheory.stoppedProcess X.X
          (fun η => (σ η : WithTop ℝ≥0)) u ω -
        Function.leftLim
          (fun r : ℝ≥0 => MeasureTheory.stoppedProcess X.X
            (fun η => (σ η : WithTop ℝ≥0)) r ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        MeasureTheory.stoppedProcess X.X
          (fun η => (σ η : WithTop ℝ≥0)) u ω -
          Function.leftLim
            (fun r : ℝ≥0 => MeasureTheory.stoppedProcess X.X
              (fun η => (σ η : WithTop ℝ≥0)) r ω) u)))
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(SNX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal))) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(SNX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal))) ∂P) = 0 := by
  intro NX K M hM T S hST hS MT N hMT μ hμclock hN τ hτ σ hσeq G hGm hGiN H hH hSupport
  letI : IsProbabilityMeasure P := X.isProbability
  have hBase :=
    avram_p2_e_compensator_literal_original_stopped_signed_L1_physical_clock
      X M hM T S hST hS MT N hMT μ hμclock hN
      τ hτ G hGm hGiN H hH hSupport
  have hMask (ω : Ω) (p : ℝ≥0 × ℝ) :
      ({p : ℝ≥0 × ℝ | p.1 ≤ σ ω}).indicator
        (fun p => H ((p.1, ω), p.2)) p = H ((p.1, ω), p.2) := by
    by_cases hp : p.1 ≤ σ ω
    · simp [hp]
    · have hNot : ¬ (p.1 : ℝ≥0∞) ≤ τ ω := by
        simpa [hσeq ω, ENNReal.coe_le_coe] using hp
      rw [hH]
      simp [hp, hNot]
  have hPath (ω : Ω) :=
    (avram_ftap_original_stopped_NX_marked_integral_indicator X σ ω).1
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2))
  simp_rw [hMask] at hPath
  simp_rw [← hPath] at hBase
  simpa only using hBase
