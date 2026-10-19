-- Prove2me | solution 1 for CohnElkies.schwartz_imaginaryRiesz_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/0cb11733-8e3c-4849-b29a-8ea41ea8f797

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
    (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    Integrable
      (fun x : Euclidean d =>
        f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))) := by
  apply schwartz_mul_norm_cpow_integrable
    hd f (-(Complex.I * (t : ℂ)))
  · norm_num
    exact Nat.cast_pos.mpr hd
  · norm_num
end CohnElkies
