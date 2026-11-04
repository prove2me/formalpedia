-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_monotone_path_continuous_of_leftLim_and_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:16:36.939227+00:00
-- url     : https://prove2.me/submissions/dd4d82e1-5371-4693-aa90-8813dd256bc2

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

/-- A monotone real-valued path without a positive-time left jump,
whose right limit agrees with its value, is continuous at that time. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hm : Monotone f) (t : ℝ≥0) (ht : 0 < t)
    (hl : Function.leftLim f t = f t)
    (hr : Filter.Tendsto f (𝓝[>] t) (nhds (f t))) :
    ContinuousAt f t := by
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hright : Function.rightLim f t = f t :=
    rightLim_eq_of_tendsto hr
  exact (hm.continuousAt_iff_leftLim_eq_rightLim).2
    (hl.trans hright.symm)
