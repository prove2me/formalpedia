-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_ubv_original_nonmonotone_cofinal_overshooting_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:35:58.734424+00:00
-- url     : https://prove2.me/submissions/a7000e3e-c336-49a6-969d-7bc2465ba8e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_overshooting_liminf_fatou_no_extra_nonneg

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
    (τ : ℕ → Ω → ℝ≥0∞) (hτmeas : ∀ n, Measurable (τ n))
    (hτliminfLowerAE : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (hBudgetCofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  choose pick hpick using hBudgetCofinal
  let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => τ (pick n) ω
  have hσmeas : ∀ n, Measurable (σ n) := fun n => hτmeas (pick n)
  have hσliminfLowerAE : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, σ (n + k) ω) := by
    filter_upwards [hτliminfLowerAE] with ω hω
    refine hω.trans ?_
    refine iSup_le fun n => ?_
    have htail : (⨅ k : ℕ, τ (n + k) ω) ≤
        (⨅ k : ℕ, τ (pick (n + k)) ω) := by
      refine le_iInf fun k => ?_
      have hge : n ≤ pick (n + k) :=
        (Nat.le_add_right n k).trans (hpick (n + k)).1
      have hindex : n + (pick (n + k) - n) = pick (n + k) := by omega
      have hle := iInf_le (fun j : ℕ => τ (n + j) ω) (pick (n + k) - n)
      simpa only [hindex] using hle
    exact htail.trans
      (le_iSup (fun m : ℕ => ⨅ k : ℕ, τ (pick (m + k)) ω) n)
  have hσBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) :=
    fun n => (hpick n).2
  exact avram_wave5_ubv_original_overshooting_liminf_fatou_no_extra_nonneg
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hjump T hT σ hσmeas hσliminfLowerAE hσBudget
end
