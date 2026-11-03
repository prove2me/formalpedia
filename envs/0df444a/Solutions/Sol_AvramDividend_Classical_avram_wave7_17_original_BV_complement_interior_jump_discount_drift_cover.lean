-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_complement_interior_jump_discount_drift_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:44:57.15652+00:00
-- url     : https://prove2.me/submissions/508487ad-8e05-4fdd-b292-7f8e4284059c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x))
    (y : ℝ) (hy0 : 0 < y) (hyC : ENNReal.ofReal y < C) :
    0 < X.drift ∧ X.GeneratorIntegrable w y ∧
    X.drift ≤ q * w y -
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) := by
  obtain ⟨_, hdpos, _, _⟩ :=
    avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad
      x hx hxc D hD T hT hEnvelope
  obtain ⟨hInt, hGen⟩ := hw_gen y hy0 hyC
  have hRep := boundedVariation_generator_physical_drift_representation
    X hBV w y hInt
  have hGrad := hw_grad y hy0 hyC
  have hMul : X.drift ≤ X.drift * deriv w y := by
    calc
      X.drift = X.drift * 1 := by ring
      _ ≤ X.drift * deriv w y :=
        mul_le_mul_of_nonneg_left hGrad (le_of_lt hdpos)
  refine ⟨hdpos, hInt, ?_⟩
  linarith only [hRep, hGen, hMul]
