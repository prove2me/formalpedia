-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_bf_new_bv_smoothfit_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:50:21.995626+00:00
-- url     : https://prove2.me/submissions/b776644f-af75-45dc-bb2a-8db9b3b2e646

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Smooth fit for positive finite BV barriers follows from the Standing density branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hac : X.ν ≪ volume :=
    standing_bv_levy_absolutely_continuous X hX hbv
  exact vcstar_deriv_one_of_bv_contDiff_one X hX q hq W hW hc hcpos hbv
    (scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
      X hX q hq W hW hbv hac)
