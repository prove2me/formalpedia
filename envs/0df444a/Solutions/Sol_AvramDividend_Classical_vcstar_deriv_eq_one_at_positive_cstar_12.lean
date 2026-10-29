-- Prove2me | solution 12 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:53:42.704994+00:00
-- url     : https://prove2.me/submissions/573b2e8c-db04-4a7c-91ce-1c0be353d568

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_gaussian_tilt
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_smoothfit_of_standing
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Smooth fit for all three canonical standing regularity branches. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  rcases h_smooth with hgauss | hbv | hC2
  · exact vcstar_deriv_one_of_gaussian_tilt
      X hX q hq W hW hc hcpos hgauss
      (scaleFunction_tilted_positive_monotone X hX q hq W hW).2
  · exact avram_ws01e_bf_new_bv_smoothfit_of_standing
      X hX q hq W hW hc hcpos hbv
  · exact vcstar_deriv_one_of_contDiffOn W hc hcpos hC2
