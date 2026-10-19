-- Prove2me | solution 1 for CohnElkies.poissonLogistic_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/7099c678-c5e0-4353-a263-6e07a5467b4d

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Function.Injective poissonLogistic := by
  intro u v huv
  have heu : 1 + Real.exp (Real.pi * u) ≠ 0 := by positivity
  have hev : 1 + Real.exp (Real.pi * v) ≠ 0 := by positivity
  unfold poissonLogistic at huv
  have hexp :
      Real.exp (Real.pi * u) = Real.exp (Real.pi * v) := by
    apply (div_eq_div_iff heu hev).mp at huv
    nlinarith
  have harg : Real.pi * u = Real.pi * v :=
    Real.exp_injective hexp
  exact mul_left_cancel₀ Real.pi_ne_zero harg
end CohnElkies
