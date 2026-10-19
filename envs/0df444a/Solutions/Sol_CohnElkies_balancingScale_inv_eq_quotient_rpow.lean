-- Prove2me | solution 1 for CohnElkies.balancingScale_inv_eq_quotient_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/e7f45cd6-d63a-4f6e-9ca8-f5e9fd0c0b42

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace ENNReal NNReal
namespace CohnElkies
theorem _root_.solution {d : ℕ} (f : Admissible d) :
    (balancingScale f)⁻¹ = quotient f ^ ((d : ℝ)⁻¹) := by
  unfold balancingScale quotient
  rw [← Real.inv_rpow
    (div_pos f.fourier_zero_pos (admissible_zero_pos f)).le]
  rw [inv_div]
end CohnElkies
