-- Prove2me | solution 2 for AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:35:12.424628+00:00
-- url     : https://prove2.me/submissions/37d73be2-e14a-44ff-9513-f71edc23c364

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_next_expected_le_current_mul_twoSided
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε) (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε)) (n : ℕ) :
    (∫⁻ ω, if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
    ENNReal.ofReal (W a / W (a + ε)) *
    (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
  have hRaw :=
    killed_firstRecord_next_expected_le_current_mul_twoSided
      X hX q hq a ε ha hε n
  have hExit := two_sided_exit_before_ruin_integral_identity
    X hX q hq W hW (a + ε) a (by linarith) ha.le (by linarith)
  have hwidth : a + ε - a = ε := by ring
  rw [hwidth] at hExit
  simpa only [hExit] using hRaw
