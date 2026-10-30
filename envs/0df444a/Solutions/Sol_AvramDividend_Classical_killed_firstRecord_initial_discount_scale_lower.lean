-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_initial_discount_scale_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:18:33.10182+00:00
-- url     : https://prove2.me/submissions/aff382e0-6d51-4a80-9bb7-0c942811d6ff

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_initial_lower_of_strict_exit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-! The q-scale strict exit law gives the initial killed first-record payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a) :
    ENNReal.ofReal (ε * (W (a - ε) / W a)) ≤
      (∫⁻ ω,
      if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
  have hx0 : 0 ≤ a - ε := by linarith
  have hxa : a - ε ≤ a := by linarith
  have hScale :=
    two_sided_exit_before_ruin_integral_identity
      X hX q hq W hW a (a - ε) ha hx0 hxa
  change (∫⁻ ω,
      if twoSidedExitUpTime X (a - (a - ε)) ω <
          twoSidedExitDownTime X (-(a - ε)) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - (a - ε)) ω).toReal)))
      else 0 ∂P) =
      ENNReal.ofReal (W (a - ε) / W a) at hScale
  have hUp : a - (a - ε) = ε := by ring
  have hDown : -(a - ε) = ε - a := by ring
  have hExit : (∫⁻ ω,
      if twoSidedExitUpTime X ε ω <
          twoSidedExitDownTime X (ε - a) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X ε ω).toReal)))
      else 0 ∂P) =
      ENNReal.ofReal (W (a - ε) / W a) := by
    simpa only [hUp, hDown] using hScale
  exact killed_firstRecord_initial_lower_of_strict_exit
    X q a ε ha hε W hExit
