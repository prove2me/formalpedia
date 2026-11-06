-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_finite_source_large_negative_band_joint_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:18:34.691746+00:00
-- url     : https://prove2.me/submissions/bad4f0a6-99b5-45ec-9fd6-92f45467f960

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform original large-negative-jump quadratic energy on every finite source measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-ε))
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤)
    (U : ℝ≥0 × Ω → ℝ) (hU : ∀ p, U p ≤ K) :
    (∫⁻ p, (∫⁻ z in B,
      ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν) ∂μ) < ⊤ := by
  obtain ⟨A, hA, hBound⟩ :=
    avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
      X w hw_cont hw_neg K hK
  have hBnonpos : B ⊆ Iic (0 : ℝ) := by
    intro z hz
    have hz' : z ≤ -ε := hBsep hz
    exact le_trans hz' (by linarith)
  have hν : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite X B hB ε hε hBsep
  have hAfinite : ENNReal.ofReal A < ⊤ := ENNReal.ofReal_lt_top
  calc
    (∫⁻ p, (∫⁻ z in B,
      ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν) ∂μ)
        ≤ ∫⁻ _p : ℝ≥0 × Ω, ENNReal.ofReal A * X.ν B ∂μ := by
            apply lintegral_mono
            intro p
            exact hBound (U p) (hU p) B hB hBnonpos
    _ = ENNReal.ofReal A * X.ν B * μ univ := by simp
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hAfinite hν) hμ
