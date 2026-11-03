-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_predictable_finite_clock_negative_mark_L1_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:38:17.199834+00:00
-- url     : https://prove2.me/submissions/243e81a3-b940-4e10-82a5-143287c3159d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- An L1 original negative Lévy-mark kernel lifts to the true finite
right-continuous predictable source clock and mark product measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (g : ℝ → ℝ) (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ)))) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable (fun p : (ℝ≥0 × Ω) × ℝ => g p.2)
        (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  have hOne : Integrable (fun _ : ℝ≥0 × Ω => (1 : ℝ)) μ :=
    integrable_const 1
  simpa only [one_mul] using hOne.mul_prod hg
