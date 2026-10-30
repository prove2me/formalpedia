-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_true_horizon_split_rewards_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:58:40.65734+00:00
-- url     : https://prove2.me/submissions/cf1801ca-6724-47a0-80b2-408cc221a067

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (ω : Ω) :
    (0 ≤ if twoSidedExitUpTime X (a-x) ω <
                twoSidedExitDownTime X (-x) ω ∧
                (twoSidedExitUpTime X (a-x) ω).toNNReal ≤ T then
      Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
      else 0) ∧
    (0 ≤ if (T : ℝ≥0∞) < twoSidedExitUpTime X (a-x) ω ∧
                (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
      Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else 0) := by
  have hWnn : ∀ y, 0 ≤ W y := fun y => by
    rcases lt_or_ge y 0 with h | h
    · exact (hW.1 y h).ge
    · exact hW.2.1 y h
  constructor
  · split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (hWnn _)
    · exact le_rfl
  · split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (hWnn _)
    · exact le_rfl
