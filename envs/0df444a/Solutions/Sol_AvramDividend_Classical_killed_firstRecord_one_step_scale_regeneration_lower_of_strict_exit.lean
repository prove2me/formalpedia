-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_lower_of_strict_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:17:33.982198+00:00
-- url     : https://prove2.me/submissions/f5a2a0ae-a70a-4352-a8bc-2bbd590855f4

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstRecord_uncapped_nextRecord_trueFactor_lower
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact uncapped Markov inequality yields scale regeneration from a strict exit formula. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a)
    (hExit :
      (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q *
          ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) :
    ∀ n : ℕ,
      ENNReal.ofReal (W (a - ε) / W a) *
        (∫⁻ ω, if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
        else 0 ∂P) ≤
        (∫⁻ ω, if twoSidedExitUpTime X (((n + 2 : ℕ) : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X (((n + 2 : ℕ) : ℝ) * ε) ω).toReal)))
        else 0 ∂P) := by
  intro n
  have hb : 0 ≤ (((n + 1 : ℕ) : ℝ) * ε) :=
    mul_nonneg (by positivity) (le_of_lt hε)
  have hrec := firstRecord_uncapped_nextRecord_trueFactor_lower
    X a (((n + 1 : ℕ) : ℝ) * ε) ε q ha hb (le_of_lt hε)
  rw [hExit] at hrec
  have hstep : (((n + 1 : ℕ) : ℝ) * ε) + ε =
      (((n + 2 : ℕ) : ℝ) * ε) := by
    push_cast
    ring
  simpa only [hstep] using hrec
