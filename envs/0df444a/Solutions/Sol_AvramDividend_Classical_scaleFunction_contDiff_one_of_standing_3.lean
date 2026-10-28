-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_contDiff_one_of_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:05:26.324038+00:00
-- url     : https://prove2.me/submissions/b4d128fe-3f4c-4a7b-8254-6288f1cc97be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_infinite_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_absolutely_continuous_levy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! Standing C¹ smoothness by the three explicit condition (3.3) cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  have h33 : X.Condition33 := hX.2.2
  unfold SpectrallyNegativeLevy.Condition33 at h33
  rcases h33 with hσ | hvar | hac
  · exact scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
  · exact scaleFunction_contDiff_one_of_infinite_variation X hX q hq W hW hvar
  · exact scaleFunction_contDiff_one_of_absolutely_continuous_levy X hX q hq W hW hac
