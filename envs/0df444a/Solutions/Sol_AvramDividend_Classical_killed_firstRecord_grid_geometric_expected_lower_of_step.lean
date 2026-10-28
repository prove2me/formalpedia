-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_grid_geometric_expected_lower_of_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:57:05.401362+00:00
-- url     : https://prove2.me/submissions/a259ca01-7699-4aab-9d6f-2ebb632d5885

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_killed_record_discount_weight_le_cell
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b q h p : ℝ)
    (hq : 0 ≤ q) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (h * Real.exp (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * h) ω).toReal)))
      else 0)
    (hzero : ENNReal.ofReal (h * p) ≤ (∫⁻ ω, w 0 ω ∂P))
    (hstep : ∀ n, ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P) ≤
      (∫⁻ ω, w (n + 1) ω ∂P)) :
    ∀ n, ENNReal.ofReal (h * p ^ (n + 1)) ≤
      (∫⁻ ω, w n ω ∂P) := by
  have hgeom (n : ℕ) :
      ENNReal.ofReal h * (ENNReal.ofReal p) ^ (n + 1) ≤
        (∫⁻ ω, w n ω ∂P) := by
    induction n with
    | zero =>
      simpa [ENNReal.ofReal_mul hh] using hzero
    | succ n ih =>
      calc
        ENNReal.ofReal h * (ENNReal.ofReal p) ^ (n + 1 + 1) =
            ENNReal.ofReal p *
              (ENNReal.ofReal h * (ENNReal.ofReal p) ^ (n + 1)) := by
          simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P) :=
          mul_le_mul_of_nonneg_left ih bot_le
        _ ≤ (∫⁻ ω, w (n + 1) ω ∂P) := hstep n
  intro n
  rw [ENNReal.ofReal_mul hh, ENNReal.ofReal_pow hp (n + 1)]
  exact hgeom n
