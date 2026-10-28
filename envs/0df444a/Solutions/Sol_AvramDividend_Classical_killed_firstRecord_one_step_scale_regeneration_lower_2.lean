-- Prove2me | solution 2 for AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:12:53.7366+00:00
-- url     : https://prove2.me/submissions/b45fefea-43bf-47c2-b9ea-88e7abe7385f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided
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
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a) :
    ∀ n : ℕ,
      ENNReal.ofReal (W (a - ε) / W a) *
        (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
        (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 2 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 2 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
  classical
  intro n
  have hRaw :=
    chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided
      X q a ε ha hε n
  have hExit := two_sided_exit_before_ruin_integral_identity
    X hX q hq W hW a (a - ε) ha (by linarith) (by linarith)
  have hupper : a - (a - ε) = ε := by ring
  have hlower : -(a - ε) = ε - a := by ring
  rw [hupper, hlower] at hExit
  simpa only [hExit] using hRaw
