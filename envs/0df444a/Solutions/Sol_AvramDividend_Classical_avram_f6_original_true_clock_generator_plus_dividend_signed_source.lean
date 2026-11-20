-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_true_clock_generator_plus_dividend_signed_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T10:10:40.799548+00:00
-- url     : https://prove2.me/submissions/79742404-ab11-47f8-b6a7-4ed4cc2318a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_compact_clock_physical_generator_drift_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_subclock_caplinear_dividend_cash_drop_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0) (k : ℕ) (μ : Measure ℝ≥0)
    (hGInt : ∀ ω : Ω, Integrable
      (fun t : ℝ≥0 =>
        let Y : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
          Real.exp (-(q * (t : ℝ))) *
            (X.generator w Y - q * w Y)
        else 0) μ)
    (ω : Ω) (hPre : σ k ω = 0 ∨
      (σ k ω : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∫ t : ℝ≥0,
      let Y : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w Y - q * w Y)
      else 0 ∂μ) +
    ((∫⁻ s in Icc (0 : ℝ) (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω) -
       V (x + X.X (σ k ω) ω))) ≤ 0 := by
  have hG :=
    avram_f6_original_compact_clock_physical_generator_drift_nonpositive
      X x q w C hw_gen D σ k μ hGInt ω
  have hR :=
    avram_f6_original_true_subclock_caplinear_dividend_cash_drop_nonpositive
      X x C q hq w hw_cont hw_smooth hw_grad D hD σ k ω hPre
  exact add_nonpos hG hR
