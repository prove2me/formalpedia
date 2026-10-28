-- Prove2me | solution 1 for AvramDividend.Classical.bv_scaleDeriv_tendsto_atTop_of_C1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:14:35.071631+00:00
-- url     : https://prove2.me/submissions/06a430f1-ac56-4397-ad41-66bd2a1751d9

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by
  obtain ⟨hpos, φ, hφ, hmono⟩ :=
    AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  exact AvramDividend.Classical.scale_deriv_tendsto_atTop_of_normalized_monotone W φ hφ
    (hpos 1 one_pos) hmono hdiff
