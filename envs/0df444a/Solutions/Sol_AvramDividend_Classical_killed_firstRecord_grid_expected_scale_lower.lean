-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_grid_expected_scale_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:35:13.450482+00:00
-- url     : https://prove2.me/submissions/6ef0ca04-fc04-4d08-8cd7-4065d71d5d81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_expected_geometric_of_actual_step
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_initial_discount_scale_lower
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_one_step_scale_regeneration_lower

set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! The scale ratio lower expectation follows from its initial exit and renewal steps. -/
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
      ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
        (∫⁻ ω,
          if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (ε * Real.exp
              (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
          else 0 ∂P) := by
  let p : ℝ := W (a - ε) / W a
  let w : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
    else 0
  have hp : 0 ≤ p := div_nonneg hWleft (le_of_lt hWa)
  have hw : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 := by
    intro n ω
    rfl
  have hbase : ENNReal.ofReal (ε * p) ≤ (∫⁻ ω, w 0 ω ∂P) := by
    simpa [w, p] using
      (killed_firstRecord_initial_discount_scale_lower
        X hX q hq W hW a ε ha hε hεa hWa hWleft hWinc)
  have hstep : ∀ n,
      ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P) ≤
        (∫⁻ ω, w (n + 1) ω ∂P) := by
    intro n
    simpa only [w, p] using
      (killed_firstRecord_one_step_scale_regeneration_lower
        X hX q hq W hW a ε ha hε hεa hWa hWleft hWinc n)
  have hgeom := killed_firstRecord_expected_geometric_of_actual_step
    X a q ε p (le_of_lt hq) (le_of_lt hε) hp w hw hbase hstep
  simpa only [p, w] using hgeom
