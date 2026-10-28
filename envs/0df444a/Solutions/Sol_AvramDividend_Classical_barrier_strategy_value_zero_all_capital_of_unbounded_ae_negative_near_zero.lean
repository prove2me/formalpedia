-- Prove2me | solution 1 for AvramDividend.Classical.barrier_strategy_value_zero_all_capital_of_unbounded_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:46:39.141585+00:00
-- url     : https://prove2.me/submissions/81eddfdc-d590-415a-a502-76e0047add89

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive initial capital is paid immediately above a zero barrier, after the zero-boundary valuation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0)
    (x : ℝ) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal (barrierValue W 0 x) := by
  have hboundary :=
    barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
      X hX q hq W hW hnbv hNear
  rcases eq_or_lt_of_le hx with hzero | hpos
  · rw [← hzero]
    exact hboundary.2
  · exact barrierStrategy_above_value_of_boundary
      X q W 0 x (le_refl 0) hpos hboundary.2 hboundary.1
