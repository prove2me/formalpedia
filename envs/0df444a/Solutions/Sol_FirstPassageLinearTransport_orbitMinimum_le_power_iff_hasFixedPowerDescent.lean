-- Prove2me | solution 1 for FirstPassageLinearTransport.orbitMinimum_le_power_iff_hasFixedPowerDescent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:39.133746+00:00
-- url     : https://prove2.me/submissions/b950f1c5-75c3-4b36-b817-feff2821c986

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
import Theorems.Thm_FirstPassageLinearTransport_orbitMinimum_le_iff_reachesBelow

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {alpha : ℝ} {n : ℕ} :
    (orbitMinimum n : ℝ) ≤ (n : ℝ) ^ alpha ↔
      HasFixedPowerDescent alpha n := by
  exact orbitMinimum_le_iff_reachesBelow
end FirstPassageLinearTransport
