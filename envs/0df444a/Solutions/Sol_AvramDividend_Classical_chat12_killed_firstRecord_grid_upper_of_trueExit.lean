-- Prove2me | solution 1 for AvramDividend.Classical.chat12_killed_firstRecord_grid_upper_of_trueExit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:51:38.287107+00:00
-- url     : https://prove2.me/submissions/5f06a79f-84f8-4844-b44a-a7ddc5b313e1

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_next_expected_le_current_mul_twoSided
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_geometric_expected_upper_of_step

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
    else 0 ∂P) = ENNReal.ofReal p) :
    ∀ n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
    else 0 ∂P) ≤ ENNReal.ofReal (ε * p ^ n) := by
  let w : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
    else 0
  have hw : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (0 + (n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (0 + (n : ℝ) * ε) ω).toReal)))
      else 0 := by
    intro n ω
    simp only [zero_add, w]
  have hstep : ∀ n : ℕ,
      (∫⁻ ω, w (n + 1) ω ∂P) ≤
        ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P) := by
    intro n
    have hUpper :=
      killed_firstRecord_next_expected_le_current_mul_twoSided
        X hX q hq a ε ha hε n
    rw [hExit] at hUpper
    simpa only [w] using hUpper
  have hGeom :=
    killed_firstRecord_grid_geometric_expected_upper_of_step
      X a 0 q ε p (le_of_lt hq) (le_of_lt hε) hp w hw hstep
  intro n
  simpa only [w] using hGeom n
