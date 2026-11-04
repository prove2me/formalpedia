-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:53:26.585247+00:00
-- url     : https://prove2.me/submissions/0bcc1b6a-9ea7-4693-b5c9-0297f5492974

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Actual original stopped W and negative extension make the discounted terminal nonnegative under cap payoff positivity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwCapPos : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → 0 ≤ w y) :
    ∀ ω, 0 ≤ Real.exp (-(q * (τ ω : ℝ))) * w (W ω) := by
  have hWcap :=
    avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
      X x C D hD hxc τ W hW
  intro ω
  have hwNonneg : 0 ≤ w (W ω) := by
    by_cases hneg : W ω < 0
    · rw [hwNeg (W ω) hneg]
    · exact hwCapPos (W ω) (le_of_not_gt hneg) (hWcap ω)
  exact mul_nonneg (Real.exp_nonneg _) hwNonneg
