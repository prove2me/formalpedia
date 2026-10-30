-- Prove2me | solution 7 for AvramDividend.Classical.barrierSupValue_eq_scale_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:02:15.211449+00:00
-- url     : https://prove2.me/submissions/b30e7830-4b23-4323-bb33-e34b19097379
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_reflected_reward_of_renewal_finite_difference_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by
  -- v3 sandwich reduction (byte-distinct elaboration over v2): C1 regularity and
  -- derivative positivity feed the stopped-renewal sandwich pair into the
  -- Proved finite-difference sandwich closure.
  have hC1 :=
    AvramDividend.Classical.scaleFunction_contDiff_one
      X hX q hq W hW
  have hMemA : a ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr ha
  have hDiffOnA : DifferentiableOn ℝ W (Set.Ioi (0 : ℝ)) :=
    ContDiffOn.differentiableOn_one hC1
  have hDiffAtA : DifferentiableAt ℝ W a :=
    hDiffOnA.differentiableAt (isOpen_Ioi.mem_nhds hMemA)
  have hHasDerivA : HasDerivAt W (deriv W a) a := hDiffAtA.hasDerivAt
  have hPosA : 0 < deriv W a :=
    AvramDividend.Classical.scaleDeriv_pos
      X hX q hq W hW a ha
  have hNeA : deriv W a ≠ 0 := ne_of_gt hPosA
  have hHiA :=
    AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound
      X hX q hq W hW a ha hHasDerivA hNeA
  have hLoA :=
    AvramDividend.Classical.barrierSupValue_stopped_renewal_lower_bound
      X hX q hq W hW a ha hHasDerivA hNeA
  have hclose : barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) :=
    AvramDividend.Classical.reflected_reward_of_renewal_finite_difference_sandwich
      W a (deriv W a) hHasDerivA hNeA (barrierSupValue X a q) hLoA hHiA
  exact hclose
