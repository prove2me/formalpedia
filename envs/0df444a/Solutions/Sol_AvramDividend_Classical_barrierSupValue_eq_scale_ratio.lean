-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_eq_scale_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T01:03:06.854686+00:00
-- url     : https://prove2.me/submissions/a65d4e57-441b-457e-9dfb-57b28fff8295
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_reflected_reward_of_renewal_finite_difference_sandwich
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos

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
  have hderiv_pos : 0 < deriv W a := scaleDeriv_pos X hX q hq W hW a ha
  have hderiv_ne : deriv W a ≠ 0 := ne_of_gt hderiv_pos
  have hD : HasDerivAt W (deriv W a) a := by
    have hdifferentiable : DifferentiableAt ℝ W a := by
      by_contra hnot
      have hzero : deriv W a = 0 := deriv_zero_of_not_differentiableAt hnot
      exact hderiv_ne hzero
    exact hdifferentiable.hasDerivAt
  have hLo :=
    barrierSupValue_stopped_renewal_lower_bound X hX q hq W hW a ha hD hderiv_ne
  have hHi :=
    barrierSupValue_stopped_renewal_upper_bound X hX q hq W hW a ha hD hderiv_ne
  exact reflected_reward_of_renewal_finite_difference_sandwich
    W a (deriv W a) hD hderiv_ne (barrierSupValue X a q) hLo hHi
