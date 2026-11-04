-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finite_cap_stopped_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:04:02.66729+00:00
-- url     : https://prove2.me/submissions/d44f583d-c416-47a4-9a58-08659c33e09d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At the true source stopped clock, finite cap and the original candidate's
    zero-extension/continuity imply terminal L1 without a new moment axiom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P) :
    Integrable Term P := by
  obtain ⟨B, hB0, hBound⟩ :=
    avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
      w c hc hw_cont hw_neg
  have hWcap :=
    avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
      X x c hc hxc D hD τ W hW
  have hAbs : ∀ᵐ ω ∂P, |w (W ω)| ≤ B :=
    Filter.Eventually.of_forall (fun ω => hBound (W ω) (hWcap ω))
  have hF : Term =
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :=
    funext hTerm
  have hMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by
    simpa only [hF] using hTermMeas
  have hI :=
    avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
      X q hq τ w W hMeas B hAbs
  simpa only [hF] using hI
