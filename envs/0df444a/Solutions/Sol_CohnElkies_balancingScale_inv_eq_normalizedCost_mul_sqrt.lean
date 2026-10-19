-- Prove2me | solution 1 for CohnElkies.balancingScale_inv_eq_normalizedCost_mul_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/f40c9c9f-a306-4408-9a3c-a1d5ac7f44a7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_balancingScale_inv_eq_quotient_rpow

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace ENNReal NNReal
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (f : Admissible d) (hd : 0 < d) :
    (balancingScale f)⁻¹ = normalizedCost f * Real.sqrt (d : ℝ) := by
  rw [balancingScale_inv_eq_quotient_rpow]
  unfold normalizedCost
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  field_simp
end CohnElkies
