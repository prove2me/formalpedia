-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_ubv_original_bounded_tailinf_stopping_cofinal_budget_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:04:47.586272+00:00
-- url     : https://prove2.me/submissions/c6a2df10-8a6a-4c85-ae6f-202aaa145f70

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_bounded_nonmonotone_tailinf_stopping_localisers
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_cofinally_bounded_stochastic_fatou_no_extra_nonneg

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
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
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
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤)
    (hBudgetCofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (⨅ j : ℕ, min (ruinTime X x D ω) (S (n + j) ω))
            (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  let ρ : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    min (⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω)) (n : ℝ≥0∞)
  have hclock := avram_wave6_ubv_original_bounded_nonmonotone_tailinf_stopping_localisers
    X x C D hD S hSstop hSliminfAE
  have hρmeas : ∀ n, Measurable (ρ n) := by
    intro n
    exact (hclock.1 n).measurable'
  have hρmono : ∀ ω, Monotone (fun n => ρ n ω) := by
    simpa only [ρ] using hclock.2.2.1
  have hρsupAE : ∀ᵐ ω ∂P, (⨆ n, ρ n ω) = ruinTime X x D ω := by
    simpa only [ρ] using hclock.2.2.2
  exact avram_wave5_ubv_original_cofinally_bounded_stochastic_fatou_no_extra_nonneg
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hjump T hT ρ hρmeas hρmono hρsupAE hBudgetCofinal
end
