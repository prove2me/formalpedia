-- Prove2me | solution 2 for AvramDividend.Classical.bv_scaleDeriv_tendsto_atTop_of_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:16:24.828677+00:00
-- url     : https://prove2.me/submissions/10e39481-5373-4ca6-a026-894b46ba8dc9

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The already Proved BV tilt plus C1 regularity forces derivative growth. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by
  obtain ⟨hpos, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  exact scale_deriv_tendsto_atTop_of_normalized_monotone
    W φ hφ (hpos 1 zero_lt_one) htilt hdiff
