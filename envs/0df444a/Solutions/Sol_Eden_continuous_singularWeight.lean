-- Prove2me | solution 1 for Eden.continuous_singularWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:36.255299+00:00
-- url     : https://prove2.me/submissions/b3a19ae0-f14c-4565-9957-529e67e27ff0

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (i : ℕ) : Continuous (singularWeight i) := by
  unfold singularWeight
  fun_prop
end Eden
