-- Prove2me | solution 1 for ENNReal.cancel_common_numerator_in_division_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/12b8481d-afb8-44d0-b9dc-636b36834007

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
namespace ENNReal
theorem _root_.solution {a b c : ENNReal} (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (hc : c ≠ ⊤) :
    (a / b) / (a / c) = c / b := by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl ha) (Or.inr (ENNReal.inv_ne_zero.mpr hc)), inv_inv]
  calc
    a * b⁻¹ * (a⁻¹ * c) = (a * a⁻¹) * (c * b⁻¹) := by ac_rfl
    _ = c * b⁻¹ := by rw [ENNReal.mul_inv_cancel ha ha', one_mul]
end ENNReal
