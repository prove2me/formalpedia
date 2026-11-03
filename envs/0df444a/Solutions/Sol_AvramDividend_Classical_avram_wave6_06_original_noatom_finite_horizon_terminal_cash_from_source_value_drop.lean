-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_noatom_finite_horizon_terminal_cash_from_source_value_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:12:53.492452+00:00
-- url     : https://prove2.me/submissions/2fe4d980-2606-4488-a185-5daaeb70f5e1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original terminal cash is controlled by the source value-loss
    expectation on zero-or-strict pre-ruin clocks without a terminal atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 < q) (w V : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_pos : ∀ y : ℝ, 0 < y → 0 ≤ w y)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (hPre : ∀ᵐ ω ∂P, τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (hNoAtom : ∀ᵐ ω ∂P, rightLimit D (τ ω) ω = D (τ ω) ω)
    (hSourceValueBudget :
      (∫⁻ ω,
        ENNReal.ofReal
          (Real.exp (-(q * (τ ω : ℝ))) *
           w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) +
        ENNReal.ofReal
          (V (x + X.X (τ ω) ω) -
           V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) ∂P) ≤
      ENNReal.ofReal (w x)) :
    (∫⁻ ω,
      ENNReal.ofReal
        (Real.exp (-(q * (τ ω : ℝ))) *
         w (riskProcess X x D (τ ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hq0 : 0 ≤ q := le_of_lt hq
  have hComparison :
      (∫⁻ ω,
        ENNReal.ofReal
          (Real.exp (-(q * (τ ω : ℝ))) *
           w (riskProcess X x D (τ ω) ω)) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ∂P) ≤
      (∫⁻ ω,
        ENNReal.ofReal
          (Real.exp (-(q * (τ ω : ℝ))) *
           w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) +
        ENNReal.ofReal
          (V (x + X.X (τ ω) ω) -
           V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) ∂P) := by
    apply lintegral_mono_ae
    filter_upwards [hPre, hNoAtom] with ω hpre hno
    have hCash :=
      avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
        X x C q hq0 w V hw_cont hw_smooth hw_grad
        hVtop hVfinite D hD ω τ hpre
    have hU :
        riskProcess X x D (τ ω) ω =
          x + X.X (τ ω) ω - rightLimit D (τ ω) ω := by
      dsimp [riskProcess]
      rw [hno]
    rw [hU]
    exact add_le_add le_rfl hCash
  exact hComparison.trans hSourceValueBudget
