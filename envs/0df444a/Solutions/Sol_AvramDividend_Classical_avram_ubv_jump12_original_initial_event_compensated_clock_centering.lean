-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump12_original_initial_event_compensated_clock_centering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T18:32:33.871883+00:00
-- url     : https://prove2.me/submissions/c5705727-5a33-4ad6-9163-45d644ff2fa2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_initial_event_masked_stop
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_masked_jump_integral
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_masked_compensator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- When the same original count/compensator stopped source is centred at
every right-continuous stopping time, it is centred on an initial event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont 0] A)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (H : Ω → (ℝ≥0 × ℝ) → ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then H ω p else 0) ∂(NX ω)) -
      (∫ t, ∫ z, (if t ≤ ρ ω then H ω (t, z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    (∀ ρ : Ω → ℝ≥0,
      IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)) →
      Integrable (J ρ) P ∧ (∫ ω, J ρ ω ∂P) = 0) →
    (∫ ω in A, J σ ω ∂P) = 0 := by
  intro NX μT J hMean
  have hσA := avram_ubv_jump12_initial_event_masked_stop
    (𝓕 := 𝓕) σ hσ A hA
  have hZero := (hMean (A.indicator σ) hσA).2
  have hMask : J (A.indicator σ) = A.indicator (J σ) := by
    funext ω
    dsimp only [J]
    have hCount :=
      avram_ubv_jump12_original_initial_event_masked_jump_integral
        X A σ H ω
    have hComp :=
      avram_ubv_jump12_original_initial_event_masked_compensator
        X T A σ (fun ξ t z => H ξ (t, z)) ω
    change
      (∫ p, (if p.1 ≤ A.indicator σ ω then H ω p else 0) ∂(NX ω)) =
        A.indicator (fun ξ =>
          ∫ p, (if p.1 ≤ σ ξ then H ξ p else 0) ∂(NX ξ)) ω at hCount
    change
      (∫ t, ∫ z, (if t ≤ A.indicator σ ω then H ω (t, z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT) =
        A.indicator (fun ξ =>
          ∫ t, ∫ z, (if t ≤ σ ξ then H ξ (t, z) else 0)
            ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT) ω at hComp
    rw [hCount, hComp]
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  rw [hMask] at hZero
  have hAglobal : MeasurableSet A := (𝓕.rightCont.le 0) A hA
  simpa only [integral_indicator hAglobal] using hZero
