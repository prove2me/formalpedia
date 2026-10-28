-- Prove2me | solution 1 for AvramDividend.Classical.barrier_zero_boundary_value_package_gaussian_of_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:57:51.710344+00:00
-- url     : https://prove2.me/submissions/1f79700c-f926-4604-8e15-74dd72a68c63

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Gaussian volatility precludes bounded-variation paths, allowing the
pathwise near-zero downward regularity theorem to close the zero-cap package. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    exact (ne_of_gt hσ) hbv.1
  exact barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
    X hX q hq W hW hnbv hNear
