-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_capped_dividendMeasure_atom_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:32:03.056609+00:00
-- url     : https://prove2.me/submissions/2c22bfa2-31b2-4199-b30c-dd9c95aa5ea1

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_admissible_jump_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      dividendMeasure D ω {(t : ℝ)} ≤
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      (w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))) := by
  rw [dividendMeasure_singleton_eq_rightLimit_sub D hD.1.1 ω t]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (local_verification_capped_admissible_jump_bound X x q w C
      hw_cont hw_smooth hw_hjb D hD hxC ω t ht)
    (Real.exp_pos _).le
