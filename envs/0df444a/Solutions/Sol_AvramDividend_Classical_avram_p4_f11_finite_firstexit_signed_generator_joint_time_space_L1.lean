-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_finite_firstexit_signed_generator_joint_time_space_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:51:03.041241+00:00
-- url     : https://prove2.me/submissions/423b0ba1-81f2-40ef-8f8f-95965fbc8438
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_finite_firstexit_joint_L1_given_corrected_clock_meas
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_original_corrected_finite_two_sided_exit_clock_measurable
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hFields :
      ∃ (R Jsmall M : ℝ≥0 → Ω → ℝ),
        (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
          Tendsto (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
            atTop (𝓝 (R u ω))) ∧
        (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
          Tendsto (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
            atTop (𝓝 (Jsmall u ω))) ∧
        (∀ u : ℝ≥0, Integrable (R u) P) ∧
        (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
        (∀ a b : ℝ≥0, a ≤ b →
          ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
        (∀ a b : ℝ≥0, a ≤ b →
          ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
        (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω)
    )
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 < b → 0 < n →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      Integrable (fun p : ℝ × Ω =>
            if ENNReal.ofReal p.1 < τ p.2 ∧
              0 < 1 + X.X (Real.toNNReal p.1) p.2 ∧
              ENNReal.ofReal (1 + X.X (Real.toNNReal p.1) p.2) < C then
              Real.exp (-(q * p.1)) *
                (X.generator w (1 + X.X (Real.toNNReal p.1) p.2) -
                  q * w (1 + X.X (Real.toNNReal p.1) p.2))
            else 0)
        (((volume : Measure ℝ).restrict (Icc (0 : ℝ) (n : ℝ))).prod P) := by
  intro b n hb hn
  exact AvramDividend.Classical.avram_p4_f11_finite_firstexit_joint_L1_given_corrected_clock_meas X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad hActivity hFields hTop b n hb hn
    (AvramDividend.Classical.avram_p4_f11_original_corrected_finite_two_sided_exit_clock_measurable X b n)
