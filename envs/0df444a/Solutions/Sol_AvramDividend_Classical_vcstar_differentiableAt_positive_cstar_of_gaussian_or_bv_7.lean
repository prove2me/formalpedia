-- Prove2me | solution 7 for AvramDividend.Classical.vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:55:25.188983+00:00
-- url     : https://prove2.me/submissions/44dc345b-d40b-4387-b2d4-2e8459a0d681

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_vcstar_differentiableAt_of_two_branch_regularity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Gaussian or bounded-variation Standing gives true ordinary barrier differentiability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation) :
    DifferentiableAt ℝ (vcstar W) (cstar W).toReal := by
  have hgauss : 0 < X.σ →
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
    intro _
    exact (scaleFunction_tilted_positive_monotone X hX q hq W hW).2
  have hbv : X.BoundedVariation →
      ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
    intro hbv
    exact scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
      X hX q hq W hW hbv
      (standing_bv_levy_absolutely_continuous X hX hbv)
  exact vcstar_differentiableAt_of_two_branch_regularity
    X hX q hq W hW hc hcpos hregular hgauss hbv
