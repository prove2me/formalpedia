-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_nonmonotone_rightcont_stopping_fatou_no_extra_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:31:31.368849+00:00
-- url     : https://prove2.me/submissions/ea842e47-eba1-4d8f-afed-d84df7ea39ac

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_min_liminf_clock_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity

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
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  let τ : ℕ → Ω → ℝ≥0∞ :=
    fun n ω => min (ruinTime X x D ω) (S n ω)
  have hτmeas : ∀ n, Measurable (τ n) := by
    intro n
    exact ((ruinTime_stopping_rightCont_filtration X x D hD.1.1).min
      (hSstop n)).measurable'
  have hτliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) = ruinTime X x D ω := by
    simpa only [τ] using
      (avram_wave5_ubv_original_ruin_min_liminf_clock_eq X x D S hSliminfAE)
  exact avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hjump T hT τ hτmeas hτliminfAE hBudget
end
