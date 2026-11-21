-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f9_original_finite_stopped_expectation_le_initial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T15:31:08.469372+00:00
-- url     : https://prove2.me/submissions/ceecdf3c-b76f-424d-9693-1df288dc7c12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_horizon_exact_integral
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_upper_boundary_positive_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_interior_positive_horizon
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
    ∀ (b : ℝ) (n : ℕ), 1 ≤ b →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) * w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) ≤ w 1 := by
  classical
  intro b n hb
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero] using
      (le_of_eq (avram_p4_f11_zero_horizon_exact_integral X q w b))
  · by_cases hb1 : b = 1
    · subst b
      simpa only [sub_self] using
        (avram_p4_f11_upper_boundary_positive_horizon
          X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
          hw_smooth hw_gen hw_grad hTop n (Nat.pos_of_ne_zero hn))
    · exact avram_p4_f11_interior_positive_horizon
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad hTop b n
        (lt_of_le_of_ne hb (Ne.symm hb1)) (Nat.pos_of_ne_zero hn)
