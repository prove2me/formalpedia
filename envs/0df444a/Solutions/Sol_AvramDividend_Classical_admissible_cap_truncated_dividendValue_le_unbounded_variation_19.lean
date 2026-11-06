-- Prove2me | solution 19 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:15:19.399213+00:00
-- url     : https://prove2.me/submissions/0a2f7227-1bd7-40f6-82e6-23bceef04361
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_ubv_positive_n_bounded_ruin_clock_ito_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_actual_bounded_ruin_budgets
import Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_UBV_HJB_stopping_criteria
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
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  rcases avram_sweep18_original_UBV_HJB_stopping_criteria
    X hBV q w C hC hw_cont hw0 hw_smooth hw_hjb x hx hxc D hD
    with ⟨hwGen, hwGrad, hwNonneg, hwJump⟩
  by_cases hxZero : x = 0
  · subst x
    exact avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
      X hBV q w C hw0 hw_cont hw_smooth hwGrad D hD hwJump T hT
  have hxPositive : 0 < x := lt_of_le_of_ne hx (Ne.symm hxZero)
  apply avram_wave5_05_corrected_ubv_from_actual_bounded_ruin_budgets
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hwGen hwGrad
    x hxc D hD hwNonneg hwJump T hT
  intro n
  cases n with
  | zero =>
      simpa only [Nat.cast_zero] using
        avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
          X q x w C hw0 hw_cont hw_smooth hwGrad D hD hxc hwJump T hT
  | succ k =>
      exact avram_wave7_08_ubv_positive_n_bounded_ruin_clock_ito_budget
        X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
        hwGen hwGrad x hxPositive hxc D hD hwNonneg hwJump
        T hT (Nat.succ k) (Nat.zero_lt_succ k)
