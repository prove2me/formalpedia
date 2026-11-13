-- Prove2me | solution 1 for CountingLLL.RandomRAM.truncation_success_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:09:11.331356+00:00
-- url     : https://prove2.me/submissions/47e98f93-0f37-4fb3-9798-0f74cdcd99c6

import Theorems.Thm_CountingLLL_RandomRAM_truncation_success

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Set Ω) (f g : Ω → ℝ≥0∞) (Bf Bg : ℝ≥0∞)
    (hBf0 : Bf ≠ 0) (hBg0 : Bg ≠ 0) (hBft : Bf ≠ ⊤) (hBgt : Bg ≠ ⊤)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ Bf) (hEg : ∫⁻ ω, g ω ∂μ ≤ Bg)
    (hgood : (15 / 16 : ℝ≥0∞) ≤ μ G) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω | ω ∈ G ∧ f ω < 16 * Bf ∧ g ω < 16 * Bg} := by
  have hf' : (∫⁻ ω, f ω / Bf ∂μ) ≤ 1 := by
    simp_rw [div_eq_mul_inv, lintegral_mul_const _ hf]
    simpa [div_eq_mul_inv, ENNReal.mul_inv_cancel hBf0 hBft] using ENNReal.div_le_div_right hEf Bf
  have hg' : (∫⁻ ω, g ω / Bg ∂μ) ≤ 1 := by
    simp_rw [div_eq_mul_inv, lintegral_mul_const _ hg]
    simpa [div_eq_mul_inv, ENNReal.mul_inv_cancel hBg0 hBgt] using ENNReal.div_le_div_right hEg Bg
  have h := CountingLLL.RandomRAM.truncation_success μ G (fun ω => f ω / Bf) (fun ω => g ω / Bg)
    (hf.div_const Bf) (hg.div_const Bg) hf' hg' hgood
  simpa only [ENNReal.div_lt_iff (Or.inl hBf0) (Or.inl hBft),
    ENNReal.div_lt_iff (Or.inl hBg0) (Or.inl hBgt)] using h
