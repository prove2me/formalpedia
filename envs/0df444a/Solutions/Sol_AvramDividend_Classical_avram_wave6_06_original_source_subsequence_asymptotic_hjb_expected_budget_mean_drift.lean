-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_source_subsequence_asymptotic_hjb_expected_budget_mean_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:29:26.375412+00:00
-- url     : https://prove2.me/submissions/dc8ed94b-1cd0-4ec8-b095-eedc837ecde5

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_actual_piecewise_discounted_terminal_auto_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopped_real_cash_measurable_no_aux
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_source_subsequence_asymptotic_stieltjes_ito_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_one_sided_budget_integrability_from_measurability
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_one_sided_hjb_expected_budget_mean_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hmono : ∀ n, Monotone (u n)) (hzero : ∀ n, u n 0 = 0)
    (hcover : ∀ ω, ∀ᶠ n in atTop, τ ω ≤ u n (k n))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (W Cash Term M G H : Ω → ℝ)
    (Source Dividend : ℕ → Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
        (hSource : ∀ n ω, Source n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      ∑ i ∈ Finset.range (k n),
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i)))))
    (hDividend : ∀ n ω, Dividend n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (k n),
          ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
            E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
            E (v (i + 1)) *
              (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
            E (v (i + 1)) *
              (w (Y (v (i + 1))) -
                w (riskProcess X x D (v (i + 1)) ω)))) +
        (if pre then 0 else E (τ ω) *
          (w (riskProcess X x D (τ ω) ω) - w (Y (τ ω)))) -
        Source n ω)
    (hSourceSubsequence : ∀ᵐ ω ∂P, Tendsto (fun n => Source (φ n) ω) atTop (𝓝 (M ω + G ω)))
    (hDividendApproxSubsequence : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, Dividend (φ n) ω + Cash ω ≤ H ω + ε)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0) (hGHmean : (∫ ω, G ω + H ω ∂P) ≤ 0) :
    Integrable Cash P ∧ (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
    (∫ ω, Cash ω ∂P) ≤ w x ∧
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  have hTermMeas : AEStronglyMeasurable Term P :=
    avram_wave6_06_original_actual_piecewise_discounted_terminal_auto_measurable
      X x C D hD w hw_cont hw_neg q τ hτ W Term hW hTerm
  have hCashMeas : AEStronglyMeasurable Cash P :=
    avram_wave6_06_original_rightcont_stopped_real_cash_measurable_no_aux
      X x C D hD q τ hτ Cash hCash
  have hTermGrid : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) := by
    intro ω
    rw [hTerm ω, hW ω]
  have hDstrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hUpper :=
    avram_wave6_06_original_ruin_source_subsequence_asymptotic_stieltjes_ito_upper
      X x q D hDstrategy w τ hτruin u k hmono hzero hcover
      φ hφ Term Cash M G H Source Dividend
      hTermGrid hSource hDividend hSourceSubsequence hDividendApproxSubsequence
  have hIntegrable :=
    avram_wave6_06_original_one_sided_budget_integrability_from_measurability
      X q w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD τ W Cash Term M G H hW hCash hTerm
      hTermMeas hCashMeas hMI hGI hHI hUpper
  exact avram_wave6_06_original_one_sided_hjb_expected_budget_mean_drift
    X q hq w C hC hw0 hw_cont hw_neg hw_smooth
    hw_gen hw_grad x hx hxc D hD τ T hτBound hτ hτruin
    W Cash Term M G H hW hCash hTerm
    hIntegrable.1 hIntegrable.2 hMI hGI hHI hMzero hGHmean hUpper
