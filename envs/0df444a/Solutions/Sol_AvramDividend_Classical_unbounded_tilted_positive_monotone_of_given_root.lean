-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_tilted_positive_monotone_of_given_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:27:52.008016+00:00
-- url     : https://prove2.me/submissions/afab2b01-89bb-4697-bd9c-bd2a04522485

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The genuine perpetual-infimum CDF identifies the fixed-root tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Set.Ioi 0) := by
  simpa only [neg_mul] using
    (unbounded_esscher_tilted_scale_monotone_uniform_bound
      X q hq W hW hnbv φ hφ hroot
      (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (by intro x hx; rfl)).1
