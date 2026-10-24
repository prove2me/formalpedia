-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_one_of_three_branch_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T09:51:10.212531+00:00
-- url     : https://prove2.me/submissions/54d2eec5-cfcf-479f-ae74-b8a4273f2c14

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_gaussian_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn

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
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgauss : 0 < X.σ →
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hbv : X.BoundedVariation →
      ContDiffOn ℝ 1 W (Ioi (0 : ℝ))) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  rcases h_smooth with hσ | hvar | hC2
  · exact vcstar_deriv_one_of_gaussian_tilt
      X hX q hq W hW hc hcpos hσ (hgauss hσ)
  · exact vcstar_deriv_one_of_bv_contDiff_one
      X hX q hq W hW hc hcpos hvar (hbv hvar)
  · exact vcstar_deriv_one_of_contDiffOn W hc hcpos hC2
