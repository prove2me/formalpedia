-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:41:13.087052+00:00
-- url     : https://prove2.me/submissions/4e6ecaf5-e3f6-421a-b467-9f77d7fd05e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A predictable signed nonlinear source-jump kernel dominated by one
integrable genuine Lévy-mark envelope is integrable on the true source clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (g : ℝ → ℝ) (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))))
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hHm : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      AEStronglyMeasurable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))))
    (hBound : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      ∀ᵐ p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))),
        ‖H p‖ ≤ ‖g p.2‖)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  have hOne : Integrable (fun _ : ℝ≥0 × Ω => (1 : ℝ)) μ :=
    integrable_const 1
  have hLift : Integrable
      (fun p : (ℝ≥0 × Ω) × ℝ => g p.2)
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by
    simpa only [one_mul] using hOne.mul_prod hg
  have hLiftNorm : Integrable
      (fun p : (ℝ≥0 × Ω) × ℝ => ‖g p.2‖)
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := hLift.norm
  exact hLiftNorm.mono' hHm hBound
