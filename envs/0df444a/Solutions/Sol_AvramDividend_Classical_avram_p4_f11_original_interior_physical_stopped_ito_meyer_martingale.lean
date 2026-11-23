-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_original_interior_physical_stopped_ito_meyer_martingale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:22:44.020153+00:00
-- url     : https://prove2.me/submissions/362c3e89-87ce-4afe-9acc-a1510b796975
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_physical_stopped_ito_finite_negative_activity
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_physical_stopped_ito_infinite_negative_activity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
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
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 < b → 0 < n →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      ∃ (R M : Ω → ℝ),
        Integrable R P ∧ Integrable M P ∧
        (∀ ω : Ω, R ω =
          (∫ s : ℝ in Icc (0 : ℝ) (n : ℝ),
            if ENNReal.ofReal s < τ ω ∧
              0 < 1 + X.X (Real.toNNReal s) ω ∧
              ENNReal.ofReal (1 + X.X (Real.toNNReal s) ω) < C then
              Real.exp (-(q * s)) *
                (X.generator w (1 + X.X (Real.toNNReal s) ω) -
                  q * w (1 + X.X (Real.toNNReal s) ω))
            else 0)) ∧
        (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P,
          Real.exp (-(q * ENNReal.toReal (τ ω))) *
            w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ≤
          w 1 + M ω + R ω) := by
  by_cases hActivity : X.ν (Iio (0 : ℝ)) = ⊤
  · exact AvramDividend.Classical.avram_p4_f11_physical_stopped_ito_infinite_negative_activity X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad hActivity hTop
  · exact AvramDividend.Classical.avram_p4_f11_physical_stopped_ito_finite_negative_activity X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad hActivity hTop
