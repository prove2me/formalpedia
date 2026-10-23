-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_boundedVariationOn_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:01:33.469077+00:00
-- url     : https://prove2.me/submissions/2f2abac5-eca1-4def-92f0-e4648d263dac

import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Algebra.Order.Group.Abs
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A monotone scale function has finite total variation on every compact interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a b : ℝ) :
    BoundedVariationOn W (Icc a b) := by
  have hmono : Monotone W := scaleFunction_monotone X q W hW
  have hmonoOn : MonotoneOn W (Icc a b) := by
    intro x hx y hy hxy
    exact hmono hxy
  apply hmonoOn.boundedVariationOn (C := max (|W a|) (|W b|))
  intro x hx
  exact abs_le_max_abs_abs (hmono hx.1) (hmono hx.2)
