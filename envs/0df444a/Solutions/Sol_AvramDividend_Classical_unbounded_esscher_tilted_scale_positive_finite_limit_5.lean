-- Prove2me | solution 5 for AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:42:17.744208+00:00
-- url     : https://prove2.me/submissions/b67a6f22-abe8-4d3b-bb02-205456637b1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Order.MonotoneConvergence
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_positive_finite_limit_of_corrected_exit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The no-Standing corrected killed exit identity transfers the established
positive finite Esscher-scale limit to the canonical unbounded target. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (nhds L) := by
  exact AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit_of_corrected_exit
    X q hq W hW hnbv φ hφ hroot V hV
    (fun a x ha hx0 hxa =>
      AvramDividend.Classical.unbounded_corrected_exit_scale_identity
        X q hq W hW hnbv a x ha hx0 hxa)
