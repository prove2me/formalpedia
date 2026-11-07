-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f9_original_finite_stopped_expectation_le_initial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:14:48.716709+00:00
-- url     : https://prove2.me/submissions/f6c62cca-83fd-468d-84e6-38f69a98b3da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_horizon_exact_integral
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_upper_boundary_positive_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_interior_positive_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Separate the zero clock, instantaneous upper boundary, and interior Dynkin clocks. -/
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
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 ≤ b →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
          w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) ≤ w 1 := by
  intro b n hb
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero_le :=
      le_of_eq (avram_p4_f11_zero_horizon_exact_integral X q w b)
    simpa only [Nat.cast_zero] using hzero_le
  rcases eq_or_lt_of_le hb with heq | hlt
  · subst b
    exact avram_p4_f11_upper_boundary_positive_horizon
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hTop n hn
  · exact avram_p4_f11_interior_positive_horizon
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hTop b n hlt hn
