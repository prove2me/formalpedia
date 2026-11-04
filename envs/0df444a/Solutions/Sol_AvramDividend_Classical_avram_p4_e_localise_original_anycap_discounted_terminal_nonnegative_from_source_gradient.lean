-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_anycap_discounted_terminal_nonnegative_from_source_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:04:26.839436+00:00
-- url     : https://prove2.me/submissions/bf41f69e-4d38-419b-87e2-a8e4d98f9d5e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- At the exact original ruined or surviving stopped clock, the source C²/HJB slope and w(0)≥0 force nonnegative discounted terminal for arbitrary cap C. -/
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
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ ω, 0 ≤ Real.exp (-(q * (τ ω : ℝ))) * w (W ω) := by
  have hWcap :=
    avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
      X x C D hD hxc τ W hW
  intro ω
  have hwNonneg : 0 ≤ w (W ω) := by
    by_cases hneg : W ω < 0
    · rw [hwNeg (W ω) hneg]
    · have hSec :=
        avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
          C w hwCont hwSmooth hwGrad 0 (W ω)
          (le_refl _) (le_of_not_gt hneg) (hWcap ω)
      linarith
  exact mul_nonneg (Real.exp_nonneg _) hwNonneg
