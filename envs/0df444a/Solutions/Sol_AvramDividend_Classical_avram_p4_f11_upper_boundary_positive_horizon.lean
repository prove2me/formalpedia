-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_upper_boundary_positive_horizon
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:08:04.010673+00:00
-- url     : https://prove2.me/submissions/16f3a099-c444-43c5-9350-17ce30e4d358
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_ae_positive_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_ae_eq_zero_of_ae_positive_near_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Instantaneous upward regularity at the initial reserve forces terminal equality. -/
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
    ∀ n : ℕ, 0 < n →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (1 - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
          w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) ≤ w 1 := by
  intro n hn
  letI : IsProbabilityMeasure P := X.isProbability
  have hnear := ae_positive_near_zero_of_unbounded_variation X hBV
  have hup := twoSidedExitUpTime_ae_eq_zero_of_ae_positive_near_zero X hnear
  have hτ : ∀ᵐ ω ∂P,
      min (twoSidedExitUpTimeCorrected X (1 - 1) ω)
        (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞)) = 0 := by
    filter_upwards [hup] with ω hω
    have hcorrect : twoSidedExitUpTimeCorrected X 0 ω = 0 := by
      simpa only [twoSidedExitUpTimeCorrected, twoSidedExitUpTime] using hω
    simp [hcorrect]
  have heq :
      (∫ ω, Real.exp (-(q * ENNReal.toReal
          (min (twoSidedExitUpTimeCorrected X (1 - 1) ω)
            (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))))) *
          w (1 + X.X (ENNReal.toNNReal
            (min (twoSidedExitUpTimeCorrected X (1 - 1) ω)
              (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞)))) ω) ∂P) =
        ∫ _ : Ω, w 1 ∂P := by
    apply integral_congr_ae
    filter_upwards [hτ] with ω hω
    simp only [sub_self] at hω
    simp [hω, X.X_zero]
  dsimp only
  rw [heq]
  simp
