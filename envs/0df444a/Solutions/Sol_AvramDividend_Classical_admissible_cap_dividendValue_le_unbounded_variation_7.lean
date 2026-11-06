-- Prove2me | solution 7 for AvramDividend.Classical.admissible_cap_dividendValue_le_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:00:56.278749+00:00
-- url     : https://prove2.me/submissions/c3fb4334-c4e0-4282-ae2e-2a92cbdc60ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat05_ubv_positive_initial_uniform_ruin_clock_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_dividendValue_upper
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hSmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro _
      exact hw_smooth
    · intro h
      exact False.elim (hBV h)
  obtain ⟨hGen, hGrad, hNonneg, hJump⟩ :=
    local_verification_stochastic_core_side_conditions
      X q w C hw_cont hw0 hSmooth hw_hjb x hxc D hD
  rcases eq_or_lt_of_le hx with hzero | hpos
  · subst x
    exact avram_wave6_10_ubv_original_zero_start_dividendValue_upper
      X hBV q w C hw0 hw_cont hw_smooth hGrad D hD hJump
  · rw [dividendValue_eq_iSup_truncated X q x D hD.1]
    apply iSup_le
    intro N
    apply avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
      X x D hD.1.1 q (N : ℝ) (ENNReal.ofReal (w x))
    intro n
    exact
      avram_wave6_chat05_ubv_positive_initial_uniform_ruin_clock_budget
        X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
        hGen hGrad x hpos hxc D hD hNonneg hJump
        (N : ℝ) (Nat.cast_nonneg N) n
