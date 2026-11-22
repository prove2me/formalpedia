-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_actual_stopped_discounted_spatial_Taylor_NX_energy_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:54:09.740159+00:00
-- url     : https://prove2.me/submissions/b0245aa2-0ceb-4783-8e67-1dccacfbe7dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_actual_stopped_NX_signed_compensator_L1
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
    (hEnergy : (∫⁻ p, ENNReal.ofReal (|G p|) ∂N) < ⊤)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (x q u v δ : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hSource : G = fun p =>
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (let Y := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2) p.1.1
        if Y ∈ Icc (u + δ) v then
          w (Y + p.2) - w Y -
            (if -1 < p.2 then p.2 * deriv w Y else 0)
        else 0))
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
  intro NX K M hM T S hST hS MT N hMT μ hμclock hN
    τ hτ σ hσeq G hGm hEnergy H hH
    x q u v δ w D hSource hSupport
  have hG : Integrable G N := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    change (∫⁻ p, ‖G p‖ₑ ∂N) < ⊤
    simpa only [Real.enorm_eq_ofReal_abs] using hEnergy
  exact avram_ftap_original_actual_stopped_NX_signed_compensator_L1
    X M hM T S hST hS MT N hMT μ hμclock hN
    τ hτ σ hσeq G hGm hG H hH hSupport
