-- Prove2me | solution 3 for AvramDividend.Classical.barrierSupValue_eq_scale_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:59:06.444592+00:00
-- url     : https://prove2.me/submissions/1077bc18-af7b-436d-a3e2-15c1df3dc42d
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
  -- Decomposition via the Proved finite-difference sandwich (319da48e).
  -- Analytic premises come from Open catalogue children, not sorries:
  -- C^1 from 6b0b9766 gives HasDerivAt at a via the standard Mathlib
  -- ContDiffOn -> DifferentiableOn -> DifferentiableAt chain; positivity
  -- of the derivative at a comes from Open 4052a131. The two eventual
  -- renewal bounds are Open 6b821aa5 / c6c3b1d0. No local Lean was run.
  have hC1 :=
    AvramDividend.Classical.scaleFunction_contDiff_one
      X hX q hq W hW
  have hmem : a ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr ha
  have hDiffOn : DifferentiableOn ℝ W (Set.Ioi (0 : ℝ)) :=
    ContDiffOn.differentiableOn_one hC1
  have hDiff : DifferentiableAt ℝ W a :=
    hDiffOn.differentiableAt (isOpen_Ioi.mem_nhds hmem)
  have hD : HasDerivAt W (deriv W a) a := hDiff.hasDerivAt
  have hpos : 0 < deriv W a :=
    AvramDividend.Classical.scaleDeriv_pos
      X hX q hq W hW a ha
  have hd : deriv W a ≠ 0 := ne_of_gt hpos
  have hLo :=
    AvramDividend.Classical.barrierSupValue_stopped_renewal_lower_bound
      X hX q hq W hW a ha hD hd
  have hHi :=
    AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound
      X hX q hq W hW a ha hD hd
  exact AvramDividend.Classical.reflected_reward_of_renewal_finite_difference_sandwich
    W a (deriv W a) hD hd (barrierSupValue X a q) hLo hHi
