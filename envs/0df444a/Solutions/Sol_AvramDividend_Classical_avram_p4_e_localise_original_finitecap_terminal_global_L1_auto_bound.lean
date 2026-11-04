-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:36:28.679523+00:00
-- url     : https://prove2.me/submissions/179558b9-370c-4b64-acfb-303452f10053

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_L1_from_cap_payoff_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The true original finite-cap ruin/survival terminal is globally L¹ from exactly half-line continuity and negative extension. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (hMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P) :
    Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by
  obtain ⟨B, hB, hBound⟩ :=
    avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
      w hwcont c hc
  exact avram_p4_e_localise_original_terminal_L1_from_cap_payoff_bound
    X x (ENNReal.ofReal c) D hD hxc q hq τ W hW
    w hwneg B hB hBound hMeas
