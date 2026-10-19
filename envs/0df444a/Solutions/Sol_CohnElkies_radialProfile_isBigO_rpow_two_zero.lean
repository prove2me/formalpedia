-- Prove2me | solution 1 for CohnElkies.radialProfile_isBigO_rpow_two_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/5f698558-d0d3-4500-bef8-c49cde349637

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_quadratic_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    radialProfile hd f =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => r ^ (2 : ℝ)) := by
  obtain ⟨C, hC⟩ := radialProfile_quadratic_bound hd f hf hzero
  apply IsBigO.of_bound C
  filter_upwards
    [eventually_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with r hr hrone
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hr.le 2), Real.rpow_two]
  exact hC r hr.le hrone.le
end CohnElkies
