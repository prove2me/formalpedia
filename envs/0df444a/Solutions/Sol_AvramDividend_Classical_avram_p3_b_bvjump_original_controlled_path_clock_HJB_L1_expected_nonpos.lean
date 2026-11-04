-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_path_clock_HJB_L1_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:43:11.995214+00:00
-- url     : https://prove2.me/submissions/39891eed-3c1b-4dc6-892a-27a4a04b983b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_true_clock_integrable_signed_Fubini_mean_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original source true-clock product HJB sign passes by genuine L1
Fubini to an integrable pathwise time residual with nonpositive expectation. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)
    (E : Set (ℝ≥0 × Ω))
    (hEpred : MeasurableSet[𝓕.rightCont.predictable] E)
    (hGen : ∀ p ∈ E, X.GeneratorIntegrable w (Upre p))
    (hHJB : ∀ p ∈ E, X.generator w (Upre p) - q * w (Upre p) ≤ 0)
    (F : ℝ≥0 × Ω → ℝ)
    (hF : ∀ p, F p = if p ∈ E then
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Upre p) +
          (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) -
          q * w (Upre p)) else 0)
    (hFint : Integrable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P)) :
    Integrable (fun ω => (∫ t, F (t, ω)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal))) P ∧
    (∫ ω, (∫ t, F (t, ω)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal)) ∂P) ≤ 0 := by
  have hsign :=
    avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos
      X hBV D hD x w q T Upre hUpre E hEpred hGen hHJB F hF hFint
  exact avram_p3_b_bvjump_original_true_clock_integrable_signed_Fubini_mean_bound
    (P := P) T F hFint hsign
