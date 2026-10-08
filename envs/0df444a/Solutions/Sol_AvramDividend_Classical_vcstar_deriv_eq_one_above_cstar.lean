-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_eq_one_above_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:42:14.24898+00:00
-- url     : https://prove2.me/submissions/8804a5a0-0cf5-48c3-a6eb-330ca6bd1a6a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (y : ℝ)
    (hy : (cstar W).toReal < y) :
    deriv (vcstar W) y = 1 := by
  let c : ℝ := (cstar W).toReal
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hnear :
      vcstar W =ᶠ[𝓝 y]
        (fun z : ℝ => z - c + divE (W c) (scaleDeriv W c)) := by
    filter_upwards [eventually_gt_nhds hy] with z hz
    have hz0 : 0 ≤ z := le_trans hc0 (le_of_lt hz)
    simp [vcstar, barrierValue, c, not_lt.mpr hz0, not_le.mpr hz]
  rw [hnear.deriv_eq]
  have hder :
      HasDerivAt (fun z : ℝ => z - c + divE (W c) (scaleDeriv W c)) 1 y :=
    ((hasDerivAt_id y).sub_const c).add_const _
  exact hder.deriv
