-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_ae_monotone_ae_cofinal_fatou_no_extra_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:55:26.83732+00:00
-- url     : https://prove2.me/submissions/cf7d7751-4d9a-4fd0-94e4-a429c50f2de6

import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
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
    (hτmonoAE : ∀ᵐ ω ∂P, Monotone (fun n => τ n ω))
    (hτsupAE : ∀ᵐ ω ∂P, (⨆ n, τ n ω) = ruinTime X x D ω)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  have hr : Measurable (ruinTime X x D) := ruinTime_measurable X x D hD.1.1
  let good : Set Ω := {ω | Monotone (fun n => τ n ω)}
  have hgood : MeasurableSet good := by
    have he : good = ⋂ i : ℕ, ⋂ j : ℕ, {ω | i ≤ j → τ i ω ≤ τ j ω} := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, good, Monotone]
    rw [he]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => by
      by_cases hij : i ≤ j
      · simpa [hij] using (measurableSet_le (hτmeas i) (hτmeas j))
      · simp [hij]))
  let τ' : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if ω ∈ good then τ n ω else ruinTime X x D ω
  have hm' : ∀ n, Measurable (τ' n) := fun n => (hτmeas n).ite hgood hr
  have hmo' : ∀ ω, Monotone (fun n => τ' n ω) := by
    intro ω i j hij
    by_cases hg : ω ∈ good
    · simpa [τ', hg] using (show Monotone (fun n => τ n ω) from hg) hij
    · simp [τ', hg]
  have hgAE : ∀ᵐ ω ∂P, ω ∈ good := hτmonoAE
  have hs' : ∀ᵐ ω ∂P, (⨆ n, τ' n ω) = ruinTime X x D ω := by
    filter_upwards [hgAE, hτsupAE] with ω hg hs
    simpa [τ', hg] using hs
  have hb' : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ' n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
    intro n
    calc
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ' n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
        (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
          apply lintegral_congr_ae
          filter_upwards [hgAE] with ω hg
          simp [τ', hg]
      _ ≤ ENNReal.ofReal (w x) := hBudget n
  exact avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hjump T hT τ' hm' hmo' hs' hb'
