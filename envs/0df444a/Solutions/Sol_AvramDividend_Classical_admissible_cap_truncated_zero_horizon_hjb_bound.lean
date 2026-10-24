-- Prove2me | solution 1 for AvramDividend.Classical.admissible_cap_truncated_zero_horizon_hjb_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:10:58.688399+00:00
-- url     : https://prove2.me/submissions/a8874acf-56a5-492f-980c-59094f5a1012

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_local_verification_w_nonneg_below_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_admissible_jump_bound
import Theorems.Thm_AvramDividend_Classical_truncated_zero_horizon_bound_of_initial_jump_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The HJB assumptions, cap and initial solvency control the actual
    Stieltjes time-zero dividend atom without stochastic localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have hjump : ∀ ω,
      rightLimit D 0 ω - D 0 ω ≤
        w x - w (x - (rightLimit D 0 ω - D 0 ω)) := by
    intro ω
    have hz : D 0 ω = 0 := hs.1 ω
    have hXz : X.X 0 ω = 0 := X.X_zero ω
    have h :=
      local_verification_capped_admissible_jump_bound
        X x q w C hw_cont hw_smooth hw_hjb D hD hxc ω 0 (Or.inl rfl)
    simpa [riskProcess, hz, hXz] using h
  have hpost : ∀ ω,
      0 ≤ w (x - (rightLimit D 0 ω - D 0 ω)) := by
    intro ω
    obtain ⟨hnonneg, hcap⟩ :=
      capped_postPaymentReserve_initial_state X x C D hD hxc ω
    have hw :=
      local_verification_w_nonneg_below_cap
        X q w C hw_cont hw0 hw_smooth hw_hjb
        (x + X.X 0 ω - rightLimit D 0 ω) hnonneg hcap
    have hz : D 0 ω = 0 := hs.1 ω
    have hXz : X.X 0 ω = 0 := X.X_zero ω
    simpa [hz, hXz] using hw
  exact truncated_zero_horizon_bound_of_initial_jump_secant
    X q x w D hs hjump hpost
