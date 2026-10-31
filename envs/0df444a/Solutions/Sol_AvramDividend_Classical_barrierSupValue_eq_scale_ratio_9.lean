-- Prove2me | solution 9 for AvramDividend.Classical.barrierSupValue_eq_scale_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:10:46.083826+00:00
-- url     : https://prove2.me/submissions/1564b766-81de-411b-9e47-bd2a5eebf4ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_reflected_value_of_local_differentiability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Genuine reflected Stieltjes boundary reward needs just source Standing
C1; the local stochastic value identity and positivity are already Proved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiffOn : DifferentiableOn ℝ W (Ioi 0) :=
    ContDiffOn.differentiableOn_one hC1
  have hdiff : DifferentiableAt ℝ W a :=
    hdiffOn.differentiableAt
      (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ha))
  exact (avram_wave3_02_reflected_value_of_local_differentiability
    X hX q hq W hW a ha hdiff).2.1
