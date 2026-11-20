-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_gaussian_full_nonlin_mark_joint_initial_positive_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:41:14.566451+00:00
-- url     : https://prove2.me/submissions/019c3d33-e3b8-4749-9f69-169c9bb5b79a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_canonical_clock_stopped_Taylor_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_compensated_clock_centering
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_canonical_Taylor_initial_event_centered
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable


open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
      (∫ t, ∫ z,
        (if t ≤ ρ ω then GW ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    ∀ (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont
        (fun ω => (σ ω : WithTop ℝ≥0)))
      (G : Ω → ℝ) (hGI : Integrable G P)
      (hGzero : P[G | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
      (hJI : Integrable (J σ) P)
      (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A),
      (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, G ω + J σ ω ∂P) = 0
      := by
  classical
  intro a Y H HS GW NX μT J
  intro σ hσ G hGI hGzero hJI A hA
  have hPos :
      MeasurableSet[𝓕.rightCont 0] {η : Ω | σ η ≠ 0} :=
    avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
      σ hσ
  have hEvent : MeasurableSet[𝓕.rightCont 0]
      (A ∩ {η : Ω | σ η ≠ 0}) := hA.inter hPos
  have hGint :
      (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, G ω ∂P) = 0 :=
    avram_ubv_jump11_past_event_integral_of_condexp_zero
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      G hGI hGzero (A ∩ {η : Ω | σ η ≠ 0}) hEvent
  have hJint :
      (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, J σ ω ∂P) = 0 :=
    avram_ubv_jump12_original_canonical_Taylor_initial_event_centered
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      q hq T σ hσ (A ∩ {η : Ω | σ η ≠ 0}) hEvent
  calc
    (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, G ω + J σ ω ∂P) =
        (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, G ω ∂P) +
        (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, J σ ω ∂P) := by
          exact integral_add hGI.integrableOn hJI.integrableOn
    _ = 0 := by rw [hGint, hJint, add_zero]