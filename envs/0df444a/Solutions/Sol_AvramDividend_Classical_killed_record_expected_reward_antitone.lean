-- Prove2me | solution 1 for AvramDividend.Classical.killed_record_expected_reward_antitone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:35:44.716988+00:00
-- url     : https://prove2.me/submissions/e6a76ddc-b39c-4204-bb6e-041458ef9231

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 < ε) (n : ℕ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω,
      if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
  apply lintegral_mono
  intro ω
  dsimp only
  have hmono := twoSidedExitUpTime_mono_threshold X ((n : ℝ) * ε) (((n + 1 : ℕ) : ℝ) * ε)
    (by push_cast; nlinarith) ω
  split_ifs with h1 h2
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hε.le
    apply Real.exp_le_exp.2
    have hfin : twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω ≠ ⊤ := ne_top_of_lt h1
    have := ENNReal.toReal_mono hfin hmono
    nlinarith
  · exact absurd (lt_of_le_of_lt hmono h1) h2
  · exact zero_le
  · exact le_rfl
