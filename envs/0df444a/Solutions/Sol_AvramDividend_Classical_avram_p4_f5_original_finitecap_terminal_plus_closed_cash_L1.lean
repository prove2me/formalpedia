-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f5_original_finitecap_terminal_plus_closed_cash_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:53:26.559316+00:00
-- url     : https://prove2.me/submissions/d6b42a5f-c84d-4b56-b495-7bf23391e9ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite-cap original discounted terminal and true closed Stieltjes cash
have a jointly integrable reward, including zero-clock and ruin atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P) :
    Integrable (fun ω => Term ω + Cash ω) P := by
  have hTermEq : Term =
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :=
    funext hTerm
  have hTermMeas' :
      AEStronglyMeasurable
        (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by
    rw [← hTermEq]
    exact hTermMeas
  have hTermI : Integrable Term P := by
    rw [hTermEq]
    exact avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound
      X x c hc hxc D hD q hq τ W hW w hw_cont hw_neg hTermMeas'
  exact hTermI.add hCashI
