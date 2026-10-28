-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_discounted_scale_zero_mean_forces_nonpositive_increment_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:14:46.216986+00:00
-- url     : https://prove2.me/submissions/7a19900d-7841-46af-97e9-e09baeb58047

import Theorems.Thm_AvramDividend_Classical_discounted_scale_zero_mean_forces_zero_ae
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

/-- Zero expectation of an un-killed scale reward prohibits any positive
increment when the unbounded-variation scale is strictly positive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (hW0 : W 0 = 0) (t : ℝ≥0)
    (hInt : Integrable
      (fun ω : Ω => Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) P)
    (hMean : (∫ ω : Ω, Real.exp (-(q * (t : ℝ))) *
      W (X.X t ω) ∂P) = W 0) :
    ∀ᵐ ω ∂P, X.X t ω ≤ 0 := by
  have hzero :=
    discounted_scale_zero_mean_forces_zero_ae X q W hW hW0 t hInt hMean
  have hpositive : ∀ y : ℝ, 0 < y → 0 < W y :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  filter_upwards [hzero] with ω hw
  by_contra hnot
  have hpos : 0 < X.X t ω := lt_of_not_ge hnot
  have hwpos : 0 < W (X.X t ω) := hpositive _ hpos
  rw [hw] at hwpos
  exact (lt_irrefl 0) hwpos
