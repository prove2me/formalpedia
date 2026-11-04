-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_terminal_L1_from_cap_payoff_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:24:18.632101+00:00
-- url     : https://prove2.me/submissions/ad6bb352-5713-4455-afcf-8337a238e23e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The actual stopped W with a cap-range bound yields an integrable original discounted terminal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hwCap : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → |w y| ≤ B)
    (hMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P) :
    Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by
  have hWcap :=
    avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
      X x C D hD hxc τ W hW
  have hwBound : ∀ ω, |w (W ω)| ≤ B := by
    intro ω
    by_cases hneg : W ω < 0
    · rw [hwneg (W ω) hneg, abs_zero]
      exact hB
    · exact hwCap (W ω) (le_of_not_gt hneg) (hWcap ω)
  exact avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
    X q hq τ w W hMeas B (Filter.Eventually.of_forall hwBound)
