-- Prove2me | solution 1 for CountingLLL.RandomRAM.truncation_success
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:06:55.566149+00:00
-- url     : https://prove2.me/submissions/8e9da486-f023-44e1-bb26-67760388984d

import Mathlib

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

/-- Mathematical core of the two-cutoff argument in the proof of Theorem 1.3. Here `f` and `g`
are costs normalized by their respective expected-cost bounds. -/
theorem cutoff_success {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Set Ω) (f g : Ω → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ 1) (hEg : ∫⁻ ω, g ω ∂μ ≤ 1)
    (hgood : (15 / 16 : ℝ≥0∞) ≤ μ G) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω | ω ∈ G ∧ f ω < 16 ∧ g ω < 16} := by
  let Bf : Set Ω := {ω | 16 ≤ f ω}
  let Bg : Set Ω := {ω | 16 ≤ g ω}
  let H : Set Ω := {ω | ω ∈ G ∧ f ω < 16 ∧ g ω < 16}
  have hbadf : μ Bf ≤ (1 / 16 : ℝ≥0∞) := by
    calc
      μ Bf ≤ (∫⁻ ω, f ω ∂μ) / 16 :=
        meas_ge_le_lintegral_div hf.aemeasurable (by norm_num) (by simp)
      _ ≤ 1 / 16 := ENNReal.div_le_div_right hEf 16
  have hbadg : μ Bg ≤ (1 / 16 : ℝ≥0∞) := by
    calc
      μ Bg ≤ (∫⁻ ω, g ω ∂μ) / 16 :=
        meas_ge_le_lintegral_div hg.aemeasurable (by norm_num) (by simp)
      _ ≤ 1 / 16 := ENNReal.div_le_div_right hEg 16
  have hcover : G ⊆ H ∪ (Bf ∪ Bg) := by
    intro ω hω
    by_cases h₁ : f ω < 16
    · by_cases h₂ : g ω < 16
      · exact Or.inl ⟨hω, h₁, h₂⟩
      · exact Or.inr (Or.inr (le_of_not_gt h₂))
    · exact Or.inr (Or.inl (le_of_not_gt h₁))
  have hsum : μ.real G ≤ μ.real H + (μ.real Bf + μ.real Bg) := by
    calc
      μ.real G ≤ μ.real (H ∪ (Bf ∪ Bg)) := measureReal_mono hcover
      _ ≤ μ.real H + μ.real (Bf ∪ Bg) := measureReal_union_le _ _
      _ ≤ μ.real H + (μ.real Bf + μ.real Bg) := by linarith [measureReal_union_le (μ := μ) Bf Bg]
  have hgood' : (15 / 16 : ℝ) ≤ μ.real G := by
    have := ENNReal.toReal_mono (measure_ne_top μ G) hgood
    simpa [Measure.real, ENNReal.toReal_div] using this
  have hbadf' : μ.real Bf ≤ (1 / 16 : ℝ) := by
    have := ENNReal.toReal_mono (by simp : (1 / 16 : ℝ≥0∞) ≠ ⊤) hbadf
    simpa [Measure.real, ENNReal.toReal_div] using this
  have hbadg' : μ.real Bg ≤ (1 / 16 : ℝ) := by
    have := ENNReal.toReal_mono (by simp : (1 / 16 : ℝ≥0∞) ≠ ⊤) hbadg
    simpa [Measure.real, ENNReal.toReal_div] using this
  have hreal : (13 / 16 : ℝ) ≤ μ.real H := by linarith
  have hh : (13 / 16 : ℝ≥0∞) ≤ μ H := by
    apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) (by norm_num)) (measure_ne_top μ H)).mp
    simpa [Measure.real, ENNReal.toReal_div] using hreal
  exact hh

theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Set Ω) (f g : Ω → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ 1) (hEg : ∫⁻ ω, g ω ∂μ ≤ 1)
    (hgood : (15 / 16 : ℝ≥0∞) ≤ μ G) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω | ω ∈ G ∧ f ω < 16 ∧ g ω < 16} :=
  cutoff_success μ G f g hf hg hEf hEg hgood
