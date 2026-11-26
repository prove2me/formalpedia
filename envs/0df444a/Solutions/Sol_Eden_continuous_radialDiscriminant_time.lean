-- Prove2me | solution 1 for Eden.continuous_radialDiscriminant_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:34.925289+00:00
-- url     : https://prove2.me/submissions/222aa947-526d-421f-8891-183266b152ca

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus

set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden
namespace Eden
theorem _root_.solution (s : ℝ) :
    Continuous (fun t => radialDiscriminant t s) := by
  unfold radialDiscriminant
  fun_prop
end Eden
