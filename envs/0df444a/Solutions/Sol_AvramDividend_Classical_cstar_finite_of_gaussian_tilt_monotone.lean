-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_of_gaussian_tilt_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:35:19.72885+00:00
-- url     : https://prove2.me/submissions/271ae7a0-ce15-4d9b-a941-3fc4efd093e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_normalized_monotone

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ)
    (htilt : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (hcont : ContinuousOn (deriv W) (Set.Ioi 0)) :
    cstar W < ⊤ := by
  have hW1 : 0 < W 1 :=
    scaleFunction_strict_pos_of_gaussian X q W hW hσ 1 (by norm_num)
  exact cstar_finite_of_normalized_monotone
    W φ hφ hW1 htilt hdiff hcont
