-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:32:20.682314+00:00
-- url     : https://prove2.me/submissions/29d646c9-a4a2-44dc-9bf9-c483801e92c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_uniform_stopped_budget

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
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hruin : Measurable (ruinTime X x D) := ruinTime_measurable X x D hD.1.1
  let good : Set Ω := {ω | (⨆ n, τ n ω) = ruinTime X x D ω}
  have hsup_meas : Measurable (fun ω => ⨆ n, τ n ω) := Measurable.iSup hτmeas
  have hgood : MeasurableSet good := measurableSet_eq_fun hsup_meas hruin
  let τ' : ℕ → Ω → ℝ≥0∞ := fun n ω => if ω ∈ good then τ n ω else ruinTime X x D ω
  have hmeas' : ∀ n, Measurable (τ' n) :=
    fun n => (hτmeas n).ite hgood hruin
  have hmono' : ∀ ω, Monotone (fun n => τ' n ω) := by
    intro ω n m hnm
    by_cases hw : ω ∈ good
    · simpa [τ', hw] using hτmono ω hnm
    · simp [τ', hw]
  have hsup' : ∀ ω, (⨆ n, τ' n ω) = ruinTime X x D ω := by
    intro ω
    by_cases hw : ω ∈ good
    · have h : (⨆ n, τ n ω) = ruinTime X x D ω := hw
      simpa [τ', hw] using h
    · simp [τ', hw]
  have hgood_ae : ∀ᵐ ω ∂P, ω ∈ good := hτsupAE
  have hbudget' : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ' n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
    intro n
    calc
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ' n ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
          = (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
              ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
                apply lintegral_congr_ae
                filter_upwards [hgood_ae] with ω hω
                simp [τ', hω]
      _ ≤ ENNReal.ofReal (w x) := hBudget n
  have hnonneg := avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
    X w C hw0 hw_cont hw_smooth hw_grad x D hD
  exact avram_wave5_05_corrected_ubv_from_uniform_stopped_budget
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hnonneg hjump T hT τ' hmeas' hmono' hsup' hbudget'
