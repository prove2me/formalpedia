-- Prove2me | solution 24 for AvramDividend.Classical.local_verification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:43:18.334415+00:00
-- url     : https://prove2.me/submissions/f61d8f9e-db43-46ad-917f-845664e9d8df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_uniform_HJB_stopping_criteria
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_core_positive_cap
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_ubv_stochastic_core_corrected
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
      (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  apply local_verification_from_uniform_strategy_bound X q w C
  intro x hx hxC D hD
  obtain ⟨hwGen, hwGrad, hwNonneg, hwJump⟩ :=
    avram_sweep18_original_uniform_HJB_stopping_criteria
      X q w C hC hw_cont hw0 hw_smooth hw_hjb x hx hxC D hD
  apply dividendValue_le_of_uniform_truncated_bounds
    X q x D hD.1 (ENNReal.ofReal (w x))
  intro n
  by_cases hBV : X.BoundedVariation
  · exact admissible_cap_truncated_bv_stochastic_core_positive_cap
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      (hw_smooth.2 hBV) hwGen hwGrad x hx hxC
      D hD hwNonneg hwJump (n : ℝ) (by positivity)
  · exact admissible_cap_truncated_ubv_stochastic_core_corrected
      X hX hBV q hq w C hw0 hw_cont hw_neg
      (hw_smooth.1 hBV) hwGen hwGrad x hxC
      D hD hwNonneg hwJump (n : ℝ) (by positivity)
