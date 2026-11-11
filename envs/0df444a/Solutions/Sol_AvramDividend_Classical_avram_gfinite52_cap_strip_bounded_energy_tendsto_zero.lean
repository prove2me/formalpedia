-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite52_cap_strip_bounded_energy_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:23:29.860905+00:00
-- url     : https://prove2.me/submissions/e5e70a51-a5ef-459b-921c-324e4a93401a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gfinite51_cap_strip_measure_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (c : ℝ) (b : ℕ → ℝ) (hbmono : Monotone b)
    (hb : Tendsto b atTop (𝓝 c))
    (hCapNull : μ {ω | c ≤ Y ω} = 0)
    (f : Ω → ℝ) (B : ℝ) (hf2 : ∀ ω, (f ω) ^ 2 ≤ B ^ 2) :
    Tendsto
      (fun j : ℕ => ∫⁻ ω in {ω | b j < Y ω},
        ENNReal.ofReal ((f ω) ^ 2) ∂μ)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let s : ℕ → Set Ω := fun j => {ω | b j < Y ω}
  have hOcc : Tendsto (fun j => μ (s j)) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [s] using avram_gfinite51_cap_strip_measure_tendsto_zero
      μ Y hY c b hbmono hb hCapNull
  have hBound (j : ℕ) :
      (∫⁻ ω in s j, ENNReal.ofReal ((f ω) ^ 2) ∂μ) ≤
        ENNReal.ofReal (B ^ 2) * μ (s j) := by
    calc
      (∫⁻ ω in s j, ENNReal.ofReal ((f ω) ^ 2) ∂μ) ≤
          (∫⁻ ω in s j, ENNReal.ofReal (B ^ 2) ∂μ) := by
            apply lintegral_mono
            intro ω
            exact ENNReal.ofReal_le_ofReal (hf2 ω)
      _ = ENNReal.ofReal (B ^ 2) * μ (s j) := by
        simp [mul_comm]
  have hUpper : Tendsto
      (fun j => ENNReal.ofReal (B ^ 2) * μ (s j))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hFinite : ENNReal.ofReal (B ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    simpa using (ENNReal.Tendsto.const_mul hOcc (Or.inr hFinite))
  have hZero : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞))
      atTop (𝓝 (0 : ℝ≥0∞)) := tendsto_const_nhds
  have hTarget : Tendsto
      (fun j => ∫⁻ ω in s j, ENNReal.ofReal ((f ω) ^ 2) ∂μ)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    apply Filter.Tendsto.squeeze hZero hUpper
    · intro j
      exact bot_le
    · exact hBound
  simpa [s] using hTarget
