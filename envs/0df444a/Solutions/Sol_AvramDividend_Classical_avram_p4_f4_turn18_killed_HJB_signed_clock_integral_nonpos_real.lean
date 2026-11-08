-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn18_killed_HJB_signed_clock_integral_nonpos_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:49:21.64376+00:00
-- url     : https://prove2.me/submissions/b9f080cc-0902-42f4-a882-f545d6df8e4e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (b : ℝ) (n : ℕ) :
    ∀ ω : Ω,
      let τ : Ω → ℝ≥0∞ := fun η =>
        min (twoSidedExitUpTimeCorrected X (b - 1) η)
          (min (twoSidedExitDownTimeCorrected X (-1) η) (n : ℝ≥0∞))
      (∫ s : ℝ in Icc (0 : ℝ) (n : ℝ),
        if ENNReal.ofReal s < τ ω ∧
          0 < 1 + X.X (Real.toNNReal s) ω ∧
          ENNReal.ofReal (1 + X.X (Real.toNNReal s) ω) < C then
          Real.exp (-(q * s)) *
            (X.generator w (1 + X.X (Real.toNNReal s) ω) -
              q * w (1 + X.X (Real.toNNReal s) ω))
        else 0) ≤ 0 := by
  intro ω
  apply integral_nonpos_of_ae
  filter_upwards [] with s
  split_ifs with hs
  · exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) ((hw_gen _ hs.2.1 hs.2.2).2)
  · exact le_refl _
