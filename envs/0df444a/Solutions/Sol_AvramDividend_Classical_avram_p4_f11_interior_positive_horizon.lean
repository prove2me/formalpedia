-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_interior_positive_horizon
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:58:26.924512+00:00
-- url     : https://prove2.me/submissions/985941c3-e051-45d9-bc92-091b3e138815
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_original_interior_stopped_dynkin_signed_expectation
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn18_killed_HJB_signed_clock_integral_nonpos_real
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
      (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
          w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) ≤ w 1 := by
  intro b n hb hn
  obtain ⟨R, hRI, hRsource, hBudget⟩ :=
    AvramDividend.Classical.avram_p4_f11_original_interior_stopped_dynkin_signed_expectation X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad hTop b n hb hn
  have hRle (ω : Ω) : R ω ≤ 0 := by
    rw [hRsource ω]
    exact AvramDividend.Classical.avram_p4_f4_turn18_killed_HJB_signed_clock_integral_nonpos_real X w C q hw_gen b n ω
  have hMean : (∫ ω, R ω ∂P) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [] with ω
    exact hRle ω
  exact le_trans hBudget (by linarith)
