-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:23:27.665396+00:00
-- url     : https://prove2.me/submissions/207f41bd-f049-408b-a4f1-685a3faa9125

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_integrable_source_exponential_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped terminal L1 at every finite horizon for any discount exponent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (q θ K : ℝ)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y))
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω) :
    Integrable Term P := by
  have hSrc : Integrable (fun ω => Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P :=
    avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
      X θ hθ q τ hτmeas hstop H hbound
  have hRawEq : (fun ω => Real.exp (-(q * (τ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (τ ω) ω)))) =
      (fun ω => (K * Real.exp (θ * x)) *
        Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) := by
    funext ω
    have hExp : Real.exp (-(q * (τ ω : ℝ))) *
        Real.exp (θ * (x + X.X (τ ω) ω)) =
        Real.exp (θ * x) *
          Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (-(q * (τ ω : ℝ))) *
          (K * Real.exp (θ * (x + X.X (τ ω) ω))) =
        K * (Real.exp (-(q * (τ ω : ℝ))) *
          Real.exp (θ * (x + X.X (τ ω) ω))) := by ring
      _ = K * (Real.exp (θ * x) *
          Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) := by rw [hExp]
      _ = (K * Real.exp (θ * x)) *
          Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) := by ring
  have hRawI : Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (τ ω) ω)))) P := by
    rw [hRawEq]
    exact hSrc.const_mul _
  exact avram_p4_f_assembly_original_terminal_L1_of_integrable_source_exponential_envelope
    X C x D hD τ W Term hW w q θ K hθ hK hwGrowth
    hTerm hTermMeas hTermNonneg hRawI