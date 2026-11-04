-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:26:45.591837+00:00
-- url     : https://prove2.me/submissions/a7aabbb7-c20e-4f11-a85d-f9ebbda822d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- At the true physical finite time clock, an integrable original controlled
BV discounted generator/jump drift residual has nonpositive expectation. -/
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
    (∫ p, F p ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal).prod P)) ≤ 0 := by
  apply integral_nonpos_of_ae
  exact Filter.Eventually.of_forall (by
    intro p
    rw [hF p]
    split_ifs with hp
    · exact avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos
        X hBV w (Upre p) q (p.1 : ℝ) (hGen p hp) (hHJB p hp)
    · exact le_refl 0)
