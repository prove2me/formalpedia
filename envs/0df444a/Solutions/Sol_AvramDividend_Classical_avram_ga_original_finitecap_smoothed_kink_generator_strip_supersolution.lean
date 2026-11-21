-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_smoothed_kink_generator_strip_supersolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T22:41:04.622538+00:00
-- url     : https://prove2.me/submissions/64d28a5b-3f19-4ba9-8981-7e14caa2ebfa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_one_sided_upperstrip_convolution_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : Measure ℝ) (φ g V : ℝ → ℝ)
    (hφI : Integrable φ μ) (hφpos : 0 ≤ᵐ[μ] φ)
    (hφnorm : (∫ z, φ z ∂μ) = 1)
    (hPositive : ∀ᵐ z ∂μ, 0 < z)
    (ε : ℝ) (hε : 0 < ε) (b y α : ℝ) (hα : 1 ≤ α)
    (hg : ∀ u : ℝ, g u ≤ if b < u then max X.c 0 else 0)
    (hgI : Integrable (fun z => φ z * g (y - ε*z)) μ)
    (hφkink : 0 ≤ φ ((y - b) / ε))
    (hWeak : X.generator
      (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y =
      (∫ z, φ z * g (y - ε*z) ∂μ) +
      X.σ ^ 2 / 2 * (1 - α) * φ ((y - b) / ε) / ε) :
    X.generator (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y ≤
      if b < y then max X.c 0 else 0 := by
  have hc : 0 ≤ max X.c 0 := le_max_right _ _
  have hG := avram_ga_one_sided_upperstrip_convolution_bound
    μ φ g hφI hφpos hφnorm hPositive ε hε b y
    (max X.c 0) hc hg hgI
  have hσ : 0 ≤ X.σ ^ 2 / 2 :=
    div_nonneg (sq_nonneg _) (by norm_num)
  have hα' : 1 - α ≤ 0 := by linarith
  have hneg : X.σ ^ 2 / 2 * (1 - α) *
      φ ((y - b) / ε) / ε ≤ 0 := by
    have h1 := mul_nonpos_of_nonneg_of_nonpos hσ hα'
    have h2 := mul_nonpos_of_nonpos_of_nonneg h1 hφkink
    exact div_nonpos_of_nonpos_of_nonneg h2 (le_of_lt hε)
  rw [hWeak]
  linarith
