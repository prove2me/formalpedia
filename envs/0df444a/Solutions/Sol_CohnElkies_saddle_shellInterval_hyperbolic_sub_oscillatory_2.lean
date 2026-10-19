-- Prove2me | solution 2 for CohnElkies.saddle_shellInterval_hyperbolic_sub_oscillatory
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:20.727895+00:00
-- url     : https://prove2.me/submissions/849c6af3-92ad-49dc-8265-edb17869f090

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


theorem solution
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
  have hw' : ContinuousOn w (Set.uIcc a b) := by rw [Set.uIcc_of_le hab]; exact hw
  have hA : IntervalIntegrable (fun x => w x * (Real.cosh (x * u) - 1)) MeasureTheory.volume a b :=
    (hw'.mul (by fun_prop)).intervalIntegrable
  have hB : IntervalIntegrable (fun x => w x * (Real.cos (x * T) * Real.cosh (x * u) - 1)) MeasureTheory.volume a b :=
    (hw'.mul (by fun_prop)).intervalIntegrable
  rw [← intervalIntegral.integral_sub hA hB]
  congr 1; funext x; ring

