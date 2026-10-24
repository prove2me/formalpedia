-- Prove2me | solution 4 for AvramDividend.Classical.vcstar_global_C1_bv_positive_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:03:40.971086+00:00
-- url     : https://prove2.me/submissions/d3ef0040-38b7-429e-b963-417afa0bc59b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_vcstar_C1_of_scale_C1_tilt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Original BV C1 barrier target, with sole open dependency scale C1.
Absolute continuity of the Levy measure follows from Standing and BV. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi 0) := by
  have hac : X.ν ≪ volume :=
    standing_bv_levy_absolutely_continuous X hX hbv
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
      X hX q hq W hW hbv hac
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have htilt :=
    (scaleFunction_tilted_positive_monotone_of_bv
      X hX q hq W hW hbv).2
  exact vcstar_C1_of_scale_C1_tilt X hX q hq W hW ha hreg htilt
