-- Prove2me | solution 4 for AvramDividend.Classical.barrierStrategy_cstar_value_all_capital
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:07:41.916614+00:00
-- url     : https://prove2.me/submissions/529f6516-6da6-4cf9-959a-f839074c7cb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_all_capital_of_local_diff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- The exact original cstar Stieltjes all-capital theorem reduces
to the separately owned Standing positive-axis scale C1 assertion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by
  apply avram_wave3_02_cstar_all_capital_of_local_diff X hX q hq W hW hc
  intro ha
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiffOn : DifferentiableOn ℝ W (Ioi 0) :=
    ContDiffOn.differentiableOn_one hC1
  exact hdiffOn.differentiableAt
    (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ha))
