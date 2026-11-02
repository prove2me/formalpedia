-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_eventual_budget_stochastic_fatou_no_extra_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:53:12.874058+00:00
-- url     : https://prove2.me/submissions/3d32fb94-f316-49c3-bb6f-1486cc802bc4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsupAE : ∀ᵐ ω ∂P, (⨆ n, τ n ω) = ruinTime X x D ω)
    (hBudgetEventually : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  obtain ⟨N, hBudget⟩ := hBudgetEventually
  let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => τ (n + N) ω
  have hσmeas : ∀ n, Measurable (σ n) := by
    intro n
    exact hτmeas (n + N)
  have hσmono : ∀ ω, Monotone (fun n => σ n ω) := by
    intro ω n m hnm
    exact hτmono ω (Nat.add_le_add_right hnm N)
  have hσsupAE : ∀ᵐ ω ∂P, (⨆ n, σ n ω) = ruinTime X x D ω := by
    filter_upwards [hτsupAE] with ω hω
    have hshift : (⨆ n, σ n ω) = (⨆ n, τ n ω) := by
      apply le_antisymm
      · refine iSup_le (fun n => ?_)
        exact le_iSup (fun k => τ k ω) (n + N)
      · refine iSup_le (fun k => ?_)
        exact (hτmono ω (by omega : k ≤ k + N)).trans
          (le_iSup (fun n => σ n ω) k)
    exact hshift.trans hω
  have hσBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
    intro n
    exact hBudget (n + N) (by omega)
  exact avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hjump T hT σ hσmeas hσmono hσsupAE hσBudget
end
