-- Prove2me | solution 1 for Eden.exp_fifth_lt_planar_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:21.958377+00:00
-- url     : https://prove2.me/submissions/eea078bd-08b1-49e9-965f-86e4821372c5

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    Real.exp (-c * t) < Real.exp (-4 * t) :=
  Real.exp_lt_exp.mpr (by nlinarith)
end Eden
