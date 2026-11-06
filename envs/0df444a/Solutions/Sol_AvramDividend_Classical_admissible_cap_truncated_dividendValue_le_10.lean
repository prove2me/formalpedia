-- Prove2me | solution 10 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:42:41.60698+00:00
-- url     : https://prove2.me/submissions/b4703f8e-1563-4f40-894e-dc450b719754
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  obtain ⟨hwGen, hwGrad, hwNonneg, hwJump⟩ :=
    avram_sweep18_original_uniform_HJB_stopping_criteria
      X q w C hC hw_cont hw0 hw_smooth hw_hjb x hx hxc D hD
  by_cases hBV : X.BoundedVariation
  · exact admissible_cap_truncated_bv_stochastic_core_positive_cap
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      (hw_smooth.2 hBV) hwGen hwGrad x hx hxc
      D hD hwNonneg hwJump T hT
  · exact admissible_cap_truncated_ubv_stochastic_core_corrected
      X hX hBV q hq w C hw0 hw_cont hw_neg
      (hw_smooth.1 hBV) hwGen hwGrad x hxc
      D hD hwNonneg hwJump T hT
