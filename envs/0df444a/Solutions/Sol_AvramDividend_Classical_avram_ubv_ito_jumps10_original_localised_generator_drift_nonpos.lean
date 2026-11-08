-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps10_original_localised_generator_drift_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:37:27.094943+00:00
-- url     : https://prove2.me/submissions/b1a7f2d6-b816-4fab-8945-2189aed03ab9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The discounted, ruin-stopped original-source generator drift is nonpositive
on any localisation region contained in the open spatial HJB region. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E,
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      0 < y ∧ ENNReal.ofReal y < C)
    (μ : Measure (ℝ≥0 × Ω)) :
    (∫ p : ℝ≥0 × Ω,
      if p ∈ E then
        (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
        (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
        (X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
          q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))
      else 0 ∂μ) ≤ 0 := by
  apply MeasureTheory.integral_nonpos_of_ae
  refine Filter.Eventually.of_forall (fun p => ?_)
  by_cases hp : p ∈ E
  · simp only [if_pos hp]
    have hy := hE p hp
    have hgen := (hw_gen _ hy.1 hy.2).2
    have htime : 0 ≤ (if p.1 ≤ T then
        Real.exp (-(q * (p.1 : ℝ))) else (0 : ℝ)) := by
      split_ifs <;> positivity
    have hstop : 0 ≤ (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
        then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg htime hstop) hgen
  · simp only [if_neg hp]
    exact le_rfl
