-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_Ms_into_full_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:46:17.684798+00:00
-- url     : https://prove2.me/submissions/4e299314-0dd3-44af-90e6-1eec482b253c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_compensated_source_Ms_L1_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S)
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ∞)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hBfinite : ∀ k, (X.ν.restrict (Iio (0 : ℝ))) (B k) < ∞)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGiN : Integrable G N)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hSupport : S.indicator H = H)
    (w : ℝ → ℝ) (x : ℝ)
    (Term Cash Mc Ml Gr Hr : Ω → ℝ)
    (hMc : Integrable Mc P) (hMl : Integrable Ml P)
    (hGr : Integrable Gr P) (hHr : Integrable Hr P)
    (hMc0 : (∫ ω, Mc ω ∂P) = 0)
    (hMl0 : (∫ ω, Ml ω ∂P) = 0)
    (hres : ∀ᵐ ω ∂P, Gr ω + Hr ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + Mc ω +
        ((fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ p, H p ∂N)) ω) + Ml ω + Gr ω + Hr ω) :
    ∃ Mb Gb Hb : Ω → ℝ,
      Integrable Mb P ∧ Integrable Gb P ∧ Integrable Hb P ∧
      (∫ ω, Mb ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, Gb ω + Hb ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + Mb ω + Gb ω + Hb ω) := by
  obtain ⟨hMsInt, hMs0⟩ :=
    avram_p4_f_assembly_original_stopped_compensated_source_Ms_L1_mean_zero
      X NX hNX K hK hKmeas M hM T S hST hS MT N hMT
      μ hμfinite hμclock hN B hBm hBmono hBcover hBfinite
      τ hτ G hGm hGiN H hH hSupport
  exact avram_p4_f_assembly_three_source_martingales
    w x Term Cash Mc (fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ p, H p ∂N)) Ml Gr Hr
    hMc hMsInt hMl hGr hHr hMc0 hMs0 hMl0 hres hIto
