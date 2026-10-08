-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_exponential_tilt_strict_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:31:37.74799+00:00
-- url     : https://prove2.me/submissions/49d3bd96-6890-40bc-9205-791e67bfec16

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) :
    ∀ x : ℝ, 0 < x → 0 < Real.exp (-(φ * x)) * W x := by
  have hw : ∀ x : ℝ, 0 < x → 0 < W x :=
    (scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv).1
  intro x hx
  exact mul_pos (Real.exp_pos _) (hw x hx)
