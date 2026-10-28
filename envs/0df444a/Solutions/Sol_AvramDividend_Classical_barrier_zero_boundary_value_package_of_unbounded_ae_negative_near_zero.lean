-- Prove2me | solution 1 for AvramDividend.Classical.barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:26:10.380711+00:00
-- url     : https://prove2.me/submissions/6d1f987d-e462-4785-b967-f53451b366ee

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_instant_ruin
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The unbounded-variation zero-barrier strategy boundary follows from regular negative paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  have hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 :=
    hNear.mono (fun ω hω =>
      barrierRuinTime_zero_of_near_zero_negative_path X ω hω)
  exact
    barrier_zero_boundary_value_package_of_unbounded_instant_ruin
      X hX q hq W hW hnbv hRuin