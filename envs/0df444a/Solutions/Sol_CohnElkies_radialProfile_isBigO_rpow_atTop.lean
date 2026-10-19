-- Prove2me | solution 1 for CohnElkies.radialProfile_isBigO_rpow_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/68460aeb-c27c-48da-bcbb-703f814555df

import Mathlib
import Definitions.Def_SpherePacking

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
    (hd : 0 < d) (f : TestFunction d) (a : ℝ) :
    radialProfile hd f =O[atTop]
      (fun r : ℝ => r ^ (-a)) := by
  have hschwartz :=
    (radialSchwartzProfile hd f).isBigO_cocompact_rpow (-a)
  have htop := hschwartz.mono atTop_le_cocompact
  refine htop.congr'
    (Eventually.of_forall
      (fun r : ℝ => radialSchwartzProfile_apply hd f r)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp [Real.norm_eq_abs, abs_of_pos hr]
end CohnElkies
