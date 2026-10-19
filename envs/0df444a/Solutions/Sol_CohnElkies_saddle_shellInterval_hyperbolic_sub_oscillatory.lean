-- Prove2me | solution 1 for CohnElkies.saddle_shellInterval_hyperbolic_sub_oscillatory
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/3bd29017-c893-49b6-a567-f37c89dc531e

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (w : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (T u : ℝ) :
    (∫ x in a..b,
        w x * (Real.cosh (x * u) - 1)) -
      (∫ x in a..b,
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1)) =
      ∫ x in a..b,
        w x * Real.cosh (x * u) *
          (1 - Real.cos (x * T)) := by
  have hhyper : ContinuousOn
      (fun x : ℝ =>
        w x * (Real.cosh (x * u) - 1))
      (Icc a b) := by
    apply hw.mul
    exact (by fun_prop :
      Continuous (fun x : ℝ =>
        Real.cosh (x * u) - 1)).continuousOn
  have hosc : ContinuousOn
      (fun x : ℝ =>
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1))
      (Icc a b) := by
    apply hw.mul
    exact (by fun_prop :
      Continuous (fun x : ℝ =>
        Real.cos (x * T) * Real.cosh (x * u) - 1)).continuousOn
  rw [← intervalIntegral.integral_sub
    (hhyper.intervalIntegrable_of_Icc hab)
    (hosc.intervalIntegrable_of_Icc hab)]
  apply intervalIntegral.integral_congr
  intro x hx
  ring
end CohnElkies
