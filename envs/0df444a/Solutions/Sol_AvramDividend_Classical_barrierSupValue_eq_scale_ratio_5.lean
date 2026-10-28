-- Prove2me | solution 5 for AvramDividend.Classical.barrierSupValue_eq_scale_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:50:09.420992+00:00
-- url     : https://prove2.me/submissions/18ac0a51-f981-4b04-9d83-8a3cc648e33e
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
  -- Sandwich route (variant bytes): C1 regularity plus derivative positivity
  -- feed the stopped-renewal bounds into the Proved finite-difference sandwich.
  -- Analytic premises are Open catalogue children; this file performs no
  -- stochastic analysis itself, so expect SKETCH_ACCEPTED until they discharge.
  have hContDiff :=
    AvramDividend.Classical.scaleFunction_contDiff_one
      X hX q hq W hW
  have hMem : a ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr ha
  have hDiffOn : DifferentiableOn ℝ W (Set.Ioi (0 : ℝ)) :=
    ContDiffOn.differentiableOn_one hContDiff
  have hDiffAt : DifferentiableAt ℝ W a :=
    hDiffOn.differentiableAt (isOpen_Ioi.mem_nhds hMem)
  have hDeriv : HasDerivAt W (deriv W a) a := hDiffAt.hasDerivAt
  have hPos : 0 < deriv W a :=
    AvramDividend.Classical.scaleDeriv_pos
      X hX q hq W hW a ha
  have hNe : deriv W a ≠ 0 := ne_of_gt hPos
  have hLow :=
    AvramDividend.Classical.barrierSupValue_stopped_renewal_lower_bound
      X hX q hq W hW a ha hDeriv hNe
  have hHigh :=
    AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound
      X hX q hq W hW a ha hDeriv hNe
  exact AvramDividend.Classical.reflected_reward_of_renewal_finite_difference_sandwich
    W a (deriv W a) hDeriv hNe (barrierSupValue X a q) hLow hHigh
