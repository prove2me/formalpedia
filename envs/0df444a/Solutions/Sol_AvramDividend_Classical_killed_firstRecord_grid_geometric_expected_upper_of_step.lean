-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_grid_geometric_expected_upper_of_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:38:17.941154+00:00
-- url     : https://prove2.me/submissions/39a79e72-6722-4eec-b38e-2fbf02269d3f

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_killed_record_discount_weight_le_cell
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
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
    (hstep : ∀ n,
      (∫⁻ ω, w (n + 1) ω ∂P) ≤
        ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P)) :
    ∀ n, (∫⁻ ω, w n ω ∂P) ≤ ENNReal.ofReal (h * p ^ n) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hpoint (ω : Ω) : w 0 ω ≤ ENNReal.ofReal h := by
    rw [hw 0 ω]
    simpa using
      (chat08_killed_record_discount_weight_le_cell X a b q h hq hh ω)
  have hzero : (∫⁻ ω, w 0 ω ∂P) ≤ ENNReal.ofReal h := by
    calc
      (∫⁻ ω, w 0 ω ∂P) ≤ (∫⁻ ω, ENNReal.ofReal h ∂P) :=
        lintegral_mono hpoint
      _ = ENNReal.ofReal h := by simp
  have hgeom (n : ℕ) :
      (∫⁻ ω, w n ω ∂P) ≤
        ENNReal.ofReal h * (ENNReal.ofReal p) ^ n := by
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      calc
        (∫⁻ ω, w (n + 1) ω ∂P) ≤
            ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P) := hstep n
        _ ≤ ENNReal.ofReal p *
            (ENNReal.ofReal h * (ENNReal.ofReal p) ^ n) :=
          mul_le_mul_of_nonneg_left ih (by exact bot_le)
        _ = ENNReal.ofReal h * (ENNReal.ofReal p) ^ (n + 1) := by
          simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  intro n
  have hrewrite :
      ENNReal.ofReal (h * p ^ n) =
        ENNReal.ofReal h * (ENNReal.ofReal p) ^ n := by
    rw [ENNReal.ofReal_mul hh, ENNReal.ofReal_pow hp n]
  rw [hrewrite]
  exact hgeom n
